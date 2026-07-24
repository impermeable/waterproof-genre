/-
  Test executable for verifying that WaterproofGenre/Verbose.lean elaborates
  correctly. This file combines the WaterproofGenre document genre with the
  Verbose Lean tactic language, so it requires the `dev` environment (which
  pulls in the `verbose-lean4` dependency):

    lake -Kenv=dev exe test-verbose

  Runtime checks (verified when executed):
  - Verbose.lean elaborates without hard errors.
  - The examples whose proof is left as `sorry` (e.g. "1.1.11" and "test")
    yield `declaration uses 'sorry'` warnings.
-/

/-- Check whether `sub` occurs as a substring of `s`. -/
private def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

def main : IO UInt32 := do
  -- Elaborate Verbose.lean in a subprocess and capture diagnostics. The `dev`
  -- environment flag is required so that `verbose-lean4` is on the search path.
  let result ← IO.Process.output {
    cmd := "lake"
    args := #["-Kenv=dev", "env", "lean", "WaterproofGenre/Verbose.lean"]
  }
  let output := result.stdout ++ result.stderr

  let mut failed := false

  -- Elaboration must not produce hard errors: `lean` exits non-zero on error.
  unless result.exitCode == 0 do
    IO.eprintln s!"FAIL: elaborating Verbose.lean exited with code {result.exitCode}"
    IO.eprintln s!"  output was: {output}"
    failed := true

  -- The `sorry`-based examples must still yield their `sorry` warnings.
  unless hasSubstr output "declaration uses `sorry`" do
    IO.eprintln "FAIL: expected 'declaration uses `sorry`' warning in output"
    IO.eprintln s!"  output was: {output}"
    failed := true

  if failed then
    IO.eprintln "Some Verbose.lean elaboration checks failed."
    return 1

  IO.println "All Verbose.lean elaboration checks passed!"
  return 0
