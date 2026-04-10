-- This module serves as the root of the `WaterproofGenre` library.
-- Import modules here that should be built as part of the library.

import VersoManual
import WaterproofGenre.GoalWidget

open Verso Doc Elab
open Verso ArgParse
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean
open Lean.Doc.Syntax

/-- The WaterproofGenre document genre is currently the Verso manual genre with
custom extensions defined in this package. -/
abbrev WaterproofGenre : Verso.Doc.Genre := Verso.Genre.Manual

namespace WaterproofGenre

abbrev Manual := Verso.Genre.Manual
abbrev Config := Verso.Genre.Manual.Config
abbrev HtmlSplitMode := Verso.Genre.Manual.HtmlSplitMode
abbrev TraverseState := Verso.Genre.Manual.TraverseState
abbrev TraverseContext := Verso.Genre.Manual.TraverseContext
abbrev ExtraStep := Verso.Genre.Manual.ExtraStep
abbrev manualMain := Verso.Genre.Manual.manualMain

end WaterproofGenre

namespace Verso.Genre.Manual

block_extension Block.hint where
  traverse := fun _ _ _ => pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure <| {{<div class="hint">{{← content.mapM goB}}</div>}}

block_extension Block.input where
  traverse := fun _ _ _ => pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure <| {{<div class="input">{{← content.mapM goB}}</div>}}

@[directive_expander hint]
def hint : DirectiveExpander
  | args, contents => do
    let _title ← ArgParse.run ((some <$> .positional `title .string) <|> pure none) args
    let blocks ← contents.mapM elabBlock
    let val ← ``(Verso.Doc.Block.other Block.hint #[ $blocks ,* ])
    pure #[val]

@[directive_expander input]
def input : DirectiveExpander
  | #[], stxs => do
    let args ← stxs.mapM fun stx => do
      -- Lean code blocks inside `:::input` are fragments of a surrounding `::::multilean`
      -- stream and cannot be type-checked independently.  Store them as raw code so that
      -- the surrounding multilean expander can mask them out without triggering errors.
      match stx with
      | `(block|``` $nameStx:ident $_argsStx* | $contents:str ```) =>
        if nameStx.getId == `lean then
          ``(Verso.Doc.Block.code $(Lean.quote contents.getString))
        else
          elabBlock ⟨stx⟩
      | _ => elabBlock ⟨stx⟩
    let val ← ``(Verso.Doc.Block.other Block.input #[ $[ $args ],* ])
    pure #[val]
  | _, _ => Lean.Elab.throwUnsupportedSyntax

end Verso.Genre.Manual

namespace WaterproofGenre

open _root_.Verso.Genre.Manual in
private abbrev importedHint : DirectiveExpander := hint

open _root_.Verso.Genre.Manual in
private abbrev importedInput : DirectiveExpander := input

open _root_.Verso.Genre.Manual.InlineLean in
private abbrev importedLean : CodeBlockExpanderOf LeanBlockConfig := lean

open _root_.Verso.Genre.Manual.InlineLean in
private abbrev importedMultilean : DirectiveExpanderOf LeanBlockConfig := multilean

open _root_.Verso.Genre.Manual.InlineLean in
private abbrev importedLeanSection : DirectiveExpander := leanSection

@[directive_expander hint]
def hint : DirectiveExpander := importedHint

@[directive_expander input]
def input : DirectiveExpander := importedInput

@[code_block]
def lean : CodeBlockExpanderOf LeanBlockConfig := importedLean

@[directive]
def multilean : DirectiveExpanderOf LeanBlockConfig := importedMultilean

@[directive_expander leanSection]
def leanSection : DirectiveExpander := importedLeanSection

end WaterproofGenre

-- /-! ## Chained LSP semantic token handler

-- The Lean LSP marks Verso code block contents as `string` tokens. Verso's chained handler
-- intentionally omits code content tokens, expecting Lean to provide them. However, Lean's
-- info-based token collector only emits tokens for variables (TermInfo with fvar), not for
-- keywords. This means keywords like `let`, `have`, `by`, `sorry`, `example` get no semantic
-- tokens inside code blocks.

-- We fix this by chaining a third handler that walks the info trees pushed by the Manual genre's code
-- block elaborator to find keyword atoms in the elaborated Lean syntax and emits keyword tokens for them.
-- -/
-- section LspTokens

-- open Lean Server Lsp
-- open Lean.Server.FileWorker

-- /-- A semantic token entry with absolute line/char positions. -/
-- private structure TokenEntry where
--   line      : Nat
--   startChar : Nat
--   length    : Nat
--   type      : Nat
--   modMask   : Nat

-- private def TokenEntry.ordLt (a b : TokenEntry) : Bool :=
--   a.line < b.line || (a.line == b.line && a.startChar < b.startChar)

-- /-- Decode LSP delta-encoded token data into absolute-position entries. -/
-- private meta def decodeTokenData (data : Array Nat) : Array TokenEntry := Id.run do
--   let mut line := 0
--   let mut char := 0
--   let mut entries : Array TokenEntry := #[]
--   for i in [0:data.size:5] do
--     let #[dLine, dStart, len, ty, mods] := data[i:i+5].toArray
--       | return entries
--     line := line + dLine
--     char := if dLine == 0 then char + dStart else dStart
--     entries := entries.push ⟨line, char, len, ty, mods⟩
--   return entries

-- /-- Encode absolute-position entries back to LSP delta-encoded format. -/
-- private meta def encodeTokenData (entries : Array TokenEntry) : Array Nat := Id.run do
--   let mut data : Array Nat := #[]
--   let mut lastLine := 0
--   let mut lastChar := 0
--   for ⟨line, char, len, ty, mods⟩ in entries do
--     let dLine := line - lastLine
--     let dStart := if line == lastLine then char - lastChar else char
--     data := data ++ #[dLine, dStart, len, ty, mods]
--     lastLine := line; lastChar := char
--   return data

-- /-- Walk a syntax tree collecting keyword-like atoms that should receive semantic tokens.
-- Uses the same logic as `collectSyntaxBasedSemanticTokens` in the Lean LSP. -/
-- private meta partial def collectKeywordsFromSyntax
--     (text : FileMap) (stx : Syntax) : Array TokenEntry := Id.run do
--   if noHighlightKinds.contains stx.getKind then
--     return #[]
--   if docKinds.contains stx.getKind then
--     return #[]
--   let mut tokens : Array TokenEntry := #[]
--   if stx.isOfKind choiceKind then
--     tokens := collectKeywordsFromSyntax text stx[0]
--   else
--     for arg in stx.getArgs do
--       tokens := tokens ++ collectKeywordsFromSyntax text arg
--   let Syntax.atom _ val := stx
--     | return tokens
--   let isRegularKeyword := val.length > 0 && isIdFirst val.front
--   let isHashKeyword := val.length > 1 && val.front == '#' &&
--     isIdFirst (String.Pos.Raw.get val ⟨1⟩)
--   if !isRegularKeyword && !isHashKeyword then
--     return tokens
--   let (some startPos, some endPos) := (stx.getPos?, stx.getTailPos?)
--     | return tokens
--   let startLspPos := text.utf8PosToLspPos startPos
--   let endLspPos := text.utf8PosToLspPos endPos
--   if startLspPos.line != endLspPos.line then
--     return tokens
--   let tokenType : SemanticTokenType :=
--     if val == "sorry" || val == "admit" || val == "stop" || val == "#exit"
--     then .leanSorryLike
--     else .keyword
--   tokens := tokens.push ⟨
--     startLspPos.line,
--     startLspPos.character,
--     endLspPos.character - startLspPos.character,
--     tokenType.toNat,
--     0⟩
--   return tokens

-- /-- Walk an info tree to find all command syntax pushed by code block elaborators,
-- then extract keyword tokens from them. -/
-- private meta partial def collectKeywordsFromInfoTree
--     (text : FileMap) (tree : Elab.InfoTree) : Array TokenEntry := Id.run do
--   match tree with
--   | .context _ t => return collectKeywordsFromInfoTree text t
--   | .node info children =>
--     let mut tokens : Array TokenEntry := #[]
--     match info with
--     | .ofCommandInfo ci =>
--       if ci.elaborator == `Manual.Meta.lean then
--         tokens := tokens ++ collectKeywordsFromSyntax text ci.stx
--     | _ => pure ()
--     for child in children do
--       tokens := tokens ++ collectKeywordsFromInfoTree text child
--     return tokens
--   | .hole _ => return #[]

-- /-- Collect keyword tokens from all snapshots' info trees. -/
-- private meta def collectCodeBlockKeywords
--     (text : FileMap) (snaps : List Snapshots.Snapshot) : Array TokenEntry :=
--   snaps.foldl (init := #[]) fun acc snap =>
--     acc ++ collectKeywordsFromInfoTree text snap.infoTree

-- /-- Merge new keyword tokens into the existing LSP response token data. -/
-- private meta def mergeKeywordTokens (mine : Array TokenEntry) (existing : SemanticTokens) : Array Nat :=
--   let decoded := decodeTokenData existing.data
--   encodeTokenData ((decoded ++ mine).qsort TokenEntry.ordLt)

-- open RequestM in
-- private meta def handleCodeBlockTokensFull
--     (_params : SemanticTokensParams) (prev : LspResponse SemanticTokens) (st : SemanticTokensState) :
--     RequestM (LspResponse SemanticTokens × SemanticTokensState) := do
--   let doc ← readDoc
--   let text := doc.meta.text
--   let ctx ← read
--   let (snaps, _, isComplete) ← doc.cmdSnaps.getFinishedPrefixWithTimeout 2000
--     (cancelTks := ctx.cancelTk.cancellationTasks)
--   checkCancelled
--   let keywordTokens := collectCodeBlockKeywords text snaps
--   checkCancelled
--   let response : SemanticTokens := { prev.response with data := mergeKeywordTokens keywordTokens prev.response }
--   return ({ response, isComplete }, st)

-- meta initialize
--   chainStatefulLspRequestHandler
--     "textDocument/semanticTokens/full"
--     SemanticTokensParams
--     SemanticTokens
--     SemanticTokensState
--     handleCodeBlockTokensFull
--     handleSemanticTokensDidChange

-- end LspTokens
