-- This module serves as the root of the `WaterproofGenre` library.
-- Import modules here that should be built as part of the library.
-- import WaterproofGenre.Demo

import Verso
import Lean.Elab
import Lean.DocString.Syntax
import SubVerso.Highlighting
import Init.Data.ToString.Basic
import Verso.Code
import Verso.Doc.Lsp
import WaterproofGenre.GoalWidget

open SubVerso.Highlighting
open Lean (Json ToJson FromJson)

inductive Block where
  | leanHighlighted (highlighted : Highlighted)
  | multilean (highlighted : Highlighted)
  | hint
  | input
  deriving BEq, ToJson, FromJson

section
local instance : Repr Json where
  reprPrec v := Repr.addAppParen <| "json%" ++ v.render
deriving instance Repr for Block
end

open Verso Doc
open Lean (Name Json NameMap ToJson FromJson)
open Lean Elab
open Verso ArgParse Html Code

open Verso.Doc Elab
open Lean.Quote
open Lean Doc Syntax

structure HintConfig where
  title : String

def parserInputString [Monad m] [MonadFileMap m] (str : TSyntax `str) : m String := do
  let preString := String.Pos.Raw.extract (← getFileMap).source 0 (str.raw.getPos?.getD 0)
  let mut code := ""
  let mut iter := preString.startPos
  while h : iter ≠ preString.endPos do
    let iter' := iter.next h
    if iter.get h == '\n' then code := code.push '\n'
    else
      for _ in [0:iter.get h |>.utf8Size] do
        code := code.push ' '
    iter := iter'
  code := code ++ str.getString
  return code

def processString (altStr : String) : DocElabM Highlighted := do
  let ictx := Parser.mkInputContext altStr (← getFileName)
  let cctx : Command.Context := { fileName := ← getFileName, fileMap := FileMap.ofString altStr, cancelTk? := none, snap? := none}
  let mut cmdState : Command.State := {env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes := [{header := ""}, {header := ""}]}
  let mut pstate := {pos := 0, recovering := false}
  let mut cmds := #[]

  repeat
    let scope := cmdState.scopes.head!
    let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmd, ps', messages) := Parser.parseCommand ictx pmctx pstate cmdState.messages
    pstate := ps'
    cmdState := {cmdState with messages := messages}

    cmdState ← withInfoTreeContext (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `DemoTextbook.Exts.lean, stx := cmd})) do
      let mut cmdState := cmdState
      match (← liftM <| EIO.toIO' <| (Command.elabCommand cmd cctx).run cmdState) with
      | Except.error e => logError e.toMessageData
      | Except.ok ((), s) =>
        cmdState := s

      pure cmdState

    cmds := cmds.push cmd
    if Parser.isTerminalCommand cmd then break

  setEnv cmdState.env
  for t in cmdState.infoState.trees do
    pushInfoTree t

  for msg in cmdState.messages.unreported do
    logMessage msg

  -- Highlight syntax following the Verso pattern: temporarily switch to the
  -- elaborated env/infoState so that `highlight` can resolve references.
  let mut hls := Highlighted.empty
  let origInfoSt ← getInfoState
  let origEnv ← getEnv
  try
    setInfoState cmdState.infoState
    setEnv cmdState.env
    let msgs := cmdState.messages.unreported.toArray
    for cmd in cmds do
      hls := hls ++ (← highlight cmd msgs cmdState.infoState.trees)
  finally
    setInfoState origInfoSt
    setEnv origEnv

  pure hls

@[code_block_expander _root_.lean]
def lean : CodeBlockExpander
  | _, str => do
    let altStr ← parserInputString str
    let hls ← processString altStr
    pure #[← ``(Verso.Doc.Block.other (Block.leanHighlighted $(quote hls))
      #[Verso.Doc.Block.code $(quote str.getString)])]

@[directive_expander hint]
def hint : DirectiveExpander
  | args, contents => do
    let _title ←  ArgParse.run ((some <$> .positional `title .string) <|> pure none) args
    let blocks ← contents.mapM elabBlock
    let val ← ``(Verso.Doc.Block.other Block.hint  #[ $blocks ,* ])
    pure #[val]

partial def extractString (stxs : Array Syntax) (start : String.Pos.Raw := 0) : DocElabM (String × String.Pos.Raw):= do
  let mut code := ""
  let mut lastIdx := start

  for stx in stxs do
    match stx with
    | `(block|``` $_nameStx:ident $_argsStx* | $contents:str ```) => do
      let preString := lastIdx.extract (← getFileMap).source (contents.raw.getPos?.getD 0)
      let mut iter := preString.startPos
      while h : iter ≠ preString.endPos do
        let iter' := iter.next h
        if iter.get h == '\n' then
          code := code.push '\n'
        else
          for _ in [0:iter.get h |>.utf8Size] do
            code := code.push ' '
        iter := iter'

      lastIdx := contents.raw.getTailPos?.getD lastIdx
      code := (code ++ contents.getString)
    | _ => do
      match stx.getArgs with
      | #[] => pure ()
      | args => do
        let (str, idx) ← extractString args lastIdx
        code := code ++ str
        lastIdx := idx
  pure (code, lastIdx)

@[directive_expander multilean]
def multilean : DirectiveExpander
  | #[], stxs => do
    let (str, _) ← extractString stxs
    let hls ← processString str
    let val ← ``(Verso.Doc.Block.other (Block.multilean $(quote hls))
      #[Verso.Doc.Block.code $(quote str)])
    pure #[val]
  | _, _ => Lean.Elab.throwUnsupportedSyntax

@[directive_expander input]
def input : DirectiveExpander
  | #[], stxs => do
    let args ← stxs.mapM elabBlock
    let val ← ``(Verso.Doc.Block.other Block.input #[ $[ $args ],* ])
    pure #[val]
  | _, _ => Lean.Elab.throwUnsupportedSyntax

def WaterproofGenre : Genre where
  Inline := Empty
  Block := Block
  PartMetadata := Unit
  TraverseContext := Unit
  TraverseState := Unit

instance : BEq WaterproofGenre.Block := inferInstanceAs (BEq Block)
instance : Repr WaterproofGenre.Block := inferInstanceAs (Repr Block)
instance : ToJson WaterproofGenre.Block := inferInstanceAs (ToJson Block)
instance : FromJson WaterproofGenre.Block := inferInstanceAs (FromJson Block)

/-! ## Chained LSP semantic token handler

The Lean LSP marks Verso code block contents as `string` tokens. Verso's chained handler
intentionally omits code content tokens, expecting Lean to provide them. However, Lean's
info-based token collector only emits tokens for variables (TermInfo with fvar), not for
keywords. This means keywords like `let`, `have`, `by`, `sorry`, `example` get no semantic
tokens inside code blocks.

We fix this by chaining a third handler that walks the info trees pushed by `processString` to
find keyword atoms in the elaborated Lean syntax and emits keyword tokens for them.
-/
section LspTokens

open Lean Server Lsp
open Lean.Server.FileWorker

/-- A semantic token entry with absolute line/char positions. -/
private structure TokenEntry where
  line      : Nat
  startChar : Nat
  length    : Nat
  type      : Nat
  modMask   : Nat

private def TokenEntry.ordLt (a b : TokenEntry) : Bool :=
  a.line < b.line || (a.line == b.line && a.startChar < b.startChar)

/-- Decode LSP delta-encoded token data into absolute-position entries. -/
private meta def decodeTokenData (data : Array Nat) : Array TokenEntry := Id.run do
  let mut line := 0
  let mut char := 0
  let mut entries : Array TokenEntry := #[]
  for i in [0:data.size:5] do
    let #[dLine, dStart, len, ty, mods] := data[i:i+5].toArray
      | return entries
    line := line + dLine
    char := if dLine == 0 then char + dStart else dStart
    entries := entries.push ⟨line, char, len, ty, mods⟩
  return entries

/-- Encode absolute-position entries back to LSP delta-encoded format. -/
private meta def encodeTokenData (entries : Array TokenEntry) : Array Nat := Id.run do
  let mut data : Array Nat := #[]
  let mut lastLine := 0
  let mut lastChar := 0
  for ⟨line, char, len, ty, mods⟩ in entries do
    let dLine := line - lastLine
    let dStart := if line == lastLine then char - lastChar else char
    data := data ++ #[dLine, dStart, len, ty, mods]
    lastLine := line; lastChar := char
  return data

/-- Walk a syntax tree collecting keyword-like atoms that should receive semantic tokens.
Uses the same logic as `collectSyntaxBasedSemanticTokens` in the Lean LSP. -/
private meta partial def collectKeywordsFromSyntax
    (text : FileMap) (stx : Syntax) : Array TokenEntry := Id.run do
  if noHighlightKinds.contains stx.getKind then
    return #[]
  if docKinds.contains stx.getKind then
    return #[]
  let mut tokens : Array TokenEntry := #[]
  if stx.isOfKind choiceKind then
    tokens := collectKeywordsFromSyntax text stx[0]
  else
    for arg in stx.getArgs do
      tokens := tokens ++ collectKeywordsFromSyntax text arg
  let Syntax.atom _ val := stx
    | return tokens
  let isRegularKeyword := val.length > 0 && isIdFirst val.front
  let isHashKeyword := val.length > 1 && val.front == '#' &&
    isIdFirst (String.Pos.Raw.get val ⟨1⟩)
  if !isRegularKeyword && !isHashKeyword then
    return tokens
  let (some startPos, some endPos) := (stx.getPos?, stx.getTailPos?)
    | return tokens
  let startLspPos := text.utf8PosToLspPos startPos
  let endLspPos := text.utf8PosToLspPos endPos
  if startLspPos.line != endLspPos.line then
    return tokens
  let tokenType : SemanticTokenType :=
    if val == "sorry" || val == "admit" || val == "stop" || val == "#exit"
    then .leanSorryLike
    else .keyword
  tokens := tokens.push ⟨
    startLspPos.line,
    startLspPos.character,
    endLspPos.character - startLspPos.character,
    tokenType.toNat,
    0⟩
  return tokens

/-- Walk an info tree to find all command syntax pushed by code block elaborators,
then extract keyword tokens from them. -/
private meta partial def collectKeywordsFromInfoTree
    (text : FileMap) (tree : Elab.InfoTree) : Array TokenEntry := Id.run do
  match tree with
  | .context _ t => return collectKeywordsFromInfoTree text t
  | .node info children =>
    let mut tokens : Array TokenEntry := #[]
    match info with
    | .ofCommandInfo ci =>
      if ci.elaborator == `DemoTextbook.Exts.lean then
        tokens := tokens ++ collectKeywordsFromSyntax text ci.stx
    | _ => pure ()
    for child in children do
      tokens := tokens ++ collectKeywordsFromInfoTree text child
    return tokens
  | .hole _ => return #[]

/-- Collect keyword tokens from all snapshots' info trees. -/
private meta def collectCodeBlockKeywords
    (text : FileMap) (snaps : List Snapshots.Snapshot) : Array TokenEntry :=
  snaps.foldl (init := #[]) fun acc snap =>
    acc ++ collectKeywordsFromInfoTree text snap.infoTree

/-- Merge new keyword tokens into the existing LSP response token data. -/
private meta def mergeKeywordTokens (mine : Array TokenEntry) (existing : SemanticTokens) : Array Nat :=
  let decoded := decodeTokenData existing.data
  encodeTokenData ((decoded ++ mine).qsort TokenEntry.ordLt)

open RequestM in
private meta def handleCodeBlockTokensFull
    (_params : SemanticTokensParams) (prev : LspResponse SemanticTokens) (st : SemanticTokensState) :
    RequestM (LspResponse SemanticTokens × SemanticTokensState) := do
  let doc ← readDoc
  let text := doc.meta.text
  let ctx ← read
  let (snaps, _, isComplete) ← doc.cmdSnaps.getFinishedPrefixWithTimeout 2000
    (cancelTks := ctx.cancelTk.cancellationTasks)
  checkCancelled
  let keywordTokens := collectCodeBlockKeywords text snaps
  checkCancelled
  let response : SemanticTokens := { prev.response with data := mergeKeywordTokens keywordTokens prev.response }
  return ({ response, isComplete }, st)

meta initialize
  chainStatefulLspRequestHandler
    "textDocument/semanticTokens/full"
    SemanticTokensParams
    SemanticTokens
    SemanticTokensState
    handleCodeBlockTokensFull
    handleSemanticTokensDidChange

end LspTokens
