#!/usr/bin/env python3
"""
Talk to the Lean LSP server (lake serve) and request semantic tokens for Simple.lean.
Prints the raw token data and decoded positions so we can see what the LSP returns.
"""

import json
import subprocess
import sys
import os
import time

WORKDIR = os.path.dirname(os.path.abspath(__file__))
FILE_PATH = os.path.join(WORKDIR, sys.argv[1] if len(sys.argv) > 1 else "Simple.lean")

with open(FILE_PATH, "r") as f:
    file_content = f.read()

file_uri = "file://" + FILE_PATH

# Build lines for reference
lines = file_content.split("\n")
print("=== FILE CONTENT (with line numbers) ===")
for i, line in enumerate(lines):
    print(f"  L{i:3d}: {line}")
print()

def make_message(method, params, msg_id=None):
    msg = {"jsonrpc": "2.0", "method": method, "params": params}
    if msg_id is not None:
        msg["id"] = msg_id
    return msg

def encode_message(msg):
    body = json.dumps(msg)
    header = f"Content-Length: {len(body)}\r\n\r\n"
    return (header + body).encode("utf-8")

def read_response(proc):
    """Read a single LSP JSON-RPC message from the process stdout."""
    headers = {}
    while True:
        line = proc.stdout.readline()
        if not line:
            return None
        line = line.strip()
        if line == b"":
            break
        if b":" in line:
            key, value = line.split(b":", 1)
            headers[key.strip().decode()] = value.strip().decode()

    content_length = int(headers.get("Content-Length", 0))
    if content_length == 0:
        return None
    body = proc.stdout.read(content_length)
    return json.loads(body)

# Start lake serve
print("Starting lake serve...")
proc = subprocess.Popen(
    ["lake", "serve"],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
    cwd=WORKDIR,
)

try:
    # 1. Initialize
    init_params = {
        "processId": os.getpid(),
        "capabilities": {
            "textDocument": {
                "semanticTokens": {
                    "requests": {"full": True},
                    "tokenTypes": [
                        "namespace", "type", "class", "enum", "interface",
                        "struct", "typeParameter", "parameter", "variable",
                        "property", "enumMember", "event", "function",
                        "method", "macro", "keyword", "modifier", "comment",
                        "string", "number", "regexp", "operator", "decorator",
                        "leanSorryLike", "leanDeprecated",
                    ],
                    "tokenModifiers": [],
                }
            }
        },
        "rootUri": "file://" + WORKDIR,
        "workspaceFolders": [{"uri": "file://" + WORKDIR, "name": "lsp-test"}],
    }

    proc.stdin.write(encode_message(make_message("initialize", init_params, msg_id=1)))
    proc.stdin.flush()

    # Read initialize response
    resp = read_response(proc)
    if resp and "result" in resp:
        legend = resp["result"].get("capabilities", {}).get("semanticTokensProvider", {}).get("legend", {})
        token_types = legend.get("tokenTypes", [])
        print(f"=== SERVER TOKEN TYPES ===")
        for i, t in enumerate(token_types):
            print(f"  {i}: {t}")
        print()
    else:
        print(f"Init response: {json.dumps(resp, indent=2)}")

    # 2. Send initialized notification
    proc.stdin.write(encode_message(make_message("initialized", {})))
    proc.stdin.flush()

    # 3. Open the document
    proc.stdin.write(encode_message(make_message("textDocument/didOpen", {
        "textDocument": {
            "uri": file_uri,
            "languageId": "lean4",
            "version": 1,
            "text": file_content,
        }
    })))
    proc.stdin.flush()

    # Give the server some time to process the file
    print("Waiting for server to process file...")
    # Read any notifications (diagnostics, progress, etc.)
    # We'll wait and drain for a bit
    import select
    start = time.time()
    while time.time() - start < 30:
        # Check if there's data to read
        import selectors
        sel = selectors.DefaultSelector()
        sel.register(proc.stdout, selectors.EVENT_READ)
        events = sel.select(timeout=2.0)
        sel.unregister(proc.stdout)
        sel.close()
        if events:
            msg = read_response(proc)
            if msg:
                method = msg.get("method", "")
                if method == "$/lean/fileProgress":
                    processing = msg.get("params", {}).get("processing", [])
                    if len(processing) == 0:
                        print("  File processing complete!")
                        break
                    else:
                        print(f"  Still processing: {len(processing)} ranges...")
                elif method == "textDocument/publishDiagnostics":
                    diags = msg.get("params", {}).get("diagnostics", [])
                    print(f"  Got {len(diags)} diagnostics")
                    for d in diags[:5]:
                        r = d.get("range", {})
                        print(f"    L{r['start']['line']}:{r['start']['character']}-L{r['end']['line']}:{r['end']['character']} [{d.get('severity','')}] {d.get('message','')[:80]}")
                else:
                    print(f"  Notification: {method}")
        else:
            # no data for 2 seconds
            pass

    # 4. Request semantic tokens
    print("\n=== REQUESTING SEMANTIC TOKENS ===")
    proc.stdin.write(encode_message(make_message("textDocument/semanticTokens/full", {
        "textDocument": {"uri": file_uri}
    }, msg_id=2)))
    proc.stdin.flush()

    # Read response (may need to skip notifications)
    while True:
        resp = read_response(proc)
        if resp is None:
            print("No response received")
            break
        if resp.get("id") == 2:
            break
        # skip notifications
        method = resp.get("method", "")
        if method:
            pass  # skip

    if resp and "result" in resp and resp["result"]:
        data = resp["result"].get("data", [])
        print(f"Raw token data length: {len(data)} ({len(data)//5} tokens)")
        print()

        # Decode delta-encoded tokens
        print("=== DECODED SEMANTIC TOKENS ===")
        line = 0
        char = 0
        for i in range(0, len(data), 5):
            delta_line = data[i]
            delta_char = data[i + 1]
            length = data[i + 2]
            token_type_idx = data[i + 3]
            token_mods = data[i + 4]

            if delta_line > 0:
                line += delta_line
                char = delta_char
            else:
                char += delta_char

            token_type_name = token_types[token_type_idx] if token_type_idx < len(token_types) else f"unknown({token_type_idx})"

            # Show what text is at this position in the original file
            if line < len(lines):
                src_line = lines[line]
                snippet = src_line[char:char+length] if char + length <= len(src_line) else src_line[char:] + "..."
            else:
                snippet = "<out of range>"

            print(f"  L{line:3d}:{char:3d} len={length:3d}  type={token_type_name:20s}  text={snippet!r}")

        print(f"\n=== TOTAL: {len(data)//5} tokens ===")
    elif resp and "error" in resp:
        print(f"Error: {json.dumps(resp['error'], indent=2)}")
    else:
        print(f"Unexpected response: {json.dumps(resp, indent=2)}")

    # 5. Shutdown
    proc.stdin.write(encode_message(make_message("shutdown", {}, msg_id=99)))
    proc.stdin.flush()
    read_response(proc)
    proc.stdin.write(encode_message(make_message("exit", {})))
    proc.stdin.flush()

except Exception as e:
    print(f"Error: {e}", file=sys.stderr)
    import traceback
    traceback.print_exc()
finally:
    proc.terminate()
    proc.wait(timeout=5)
