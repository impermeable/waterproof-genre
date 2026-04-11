-- This module serves as the root of the `WaterproofGenre` library.
-- Import modules here that should be built as part of the library.

import VersoManual
import WaterproofGenre.GoalWidget

open Verso Doc Elab
open Verso ArgParse
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean
open Lean.Doc.Syntax
open SubVerso.Highlighting

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

open Lean  -- Brings Term, TSyntax, quote, getRef, getFileMap, getFileName, etc. into scope.

open _root_.Verso.Genre.Manual in
private abbrev importedHint : DirectiveExpander := hint

open _root_.Verso.Genre.Manual in
private abbrev importedInput : DirectiveExpander := input

open _root_.Verso.Genre.Manual.InlineLean in
private abbrev importedLean : CodeBlockExpanderOf LeanBlockConfig := lean

open _root_.Verso.Genre.Manual.InlineLean in
private abbrev importedLeanSection : DirectiveExpander := leanSection

@[directive_expander hint]
def hint : DirectiveExpander := importedHint

@[directive_expander input]
def input : DirectiveExpander := importedInput

@[code_block]
def lean : CodeBlockExpanderOf LeanBlockConfig := importedLean

@[directive_expander leanSection]
def leanSection : DirectiveExpander := importedLeanSection

-- Re-implementations of private Verso InlineLean functions needed for our custom multilean.

private def wpExplanationMarker (idx : Nat) : String := s!"--{idx}"

private def wpUtf8Size (str : String) : Nat :=
  str.foldl (init := 0) fun acc c => acc + c.utf8Size

private def wpBlankOfSameShape (str : String) : String := Id.run do
  let mut out := ""
  for c in str do
    if c == '\n' then out := out.push '\n'
    else for _ in [0:c.utf8Size] do out := out.push ' '
  out

private def wpLineCommentOfWidth (width : Nat) (marker : String) : String :=
  if width = 0 then ""
  else
    -- Extract at most `width` UTF-8 bytes from marker (marker is ASCII so byte = char).
    let mLen := min width marker.utf8ByteSize
    let m := String.Pos.Raw.extract marker ⟨0⟩ ⟨mLen⟩
    m ++ String.ofList (List.replicate (width - m.utf8ByteSize) ' ')

private def wpExplanationPlaceholderSource (idx : Nat) (source : String) :
    ExplanationPlaceholder × String :=
  let marker := wpExplanationMarker idx
  let lines := source.splitOn "\n" |>.toArray
  let rendered := lines.mapIdx fun i line =>
    let w := wpUtf8Size line
    if i = 0 then wpLineCommentOfWidth w marker
    else if w >= 2 then wpLineCommentOfWidth w "--"
    else String.ofList (List.replicate w ' ')
  let joined := Id.run do
    let mut s := ""
    for i in [0:rendered.size] do
      s := if i = 0 then rendered[i]! else s ++ "\n" ++ rendered[i]!
    s
  ({ marker, lineCount := rendered.size }, joined)

/--
Build the combined Lean source for an `:::input` block inside `::::multilean`.

The first line of the block becomes the placeholder marker comment (so that
`splitMultileanCode` recognises the boundary), lean code inside the block is
preserved at its original byte position (so that the whole concatenated source
still elaborates), and all other lines are replaced with comment-shaped blanks.
-/
private def inputBlockSource
    (idx : Nat) (sourceText : String)
    (blockStart blockStop : String.Pos.Raw)
    (innerBlocks : Array (TSyntax `block)) :
    ExplanationPlaceholder × String :=
  let marker := wpExplanationMarker idx
  let blockStr := blockStart.extract sourceText blockStop
  -- Collect lean code ranges as byte offsets relative to blockStart.
  let leanRanges : Array (Nat × Nat) := innerBlocks.filterMap fun ib =>
    match ib with
    | `(block|``` $nameStx:ident $_args* | $contents:str ```) =>
      if nameStx.getId != `lean then none
      else
        let cs := (contents.raw.getPos?.getD blockStart).byteIdx
        let ce := (contents.raw.getTailPos?.getD blockStart).byteIdx
        if cs < blockStart.byteIdx then none
        else some (cs - blockStart.byteIdx, ce - blockStart.byteIdx)
    | _ => none
  -- Build the source line by line.
  let lines := blockStr.splitOn "\n" |>.toArray
  let out := Id.run do
    let mut out := ""
    let mut byteOffset := 0
    for lineIdx in [0:lines.size] do
      let line := lines[lineIdx]!
      let lineLen := line.utf8ByteSize
      let lineEnd := byteOffset + lineLen
      -- Keep lines that overlap with any lean code range; blank everything else.
      let inLean := leanRanges.any fun (ls, le) => ls < lineEnd && le > byteOffset
      let rendered :=
        if inLean then line
        else
          let w := wpUtf8Size line
          if lineIdx = 0 then wpLineCommentOfWidth w marker
          else if w >= 2 then wpLineCommentOfWidth w "--"
          else String.ofList (List.replicate w ' ')
      out := if lineIdx = 0 then rendered else out ++ "\n" ++ rendered
      byteOffset := lineEnd + 1   -- +1 for the '\n' separator
    out
  ({ marker, lineCount := lines.size }, out)

/-- Quote a `Highlighted` value into a term that reconstructs it at runtime. -/
private def wpQuoteHighlight (hls : Highlighted) : DocElabM Term := do
  let repr := hlToExport hls
  ``(hlFromExport! $(quote repr))

/-- Produce a `Block.multilean` block term from highlighting data and explanation content. -/
private def wpToHighlightedMultileanBlock
    (placeholders : Array ExplanationPlaceholder) (content : Array Term)
    (shouldShow : Bool) (hls : Highlighted) : DocElabM Term := do
  if !shouldShow then return ← ``(Block.concat #[])
  let range := (← getRef).getRange? |>.map (← getFileMap).utf8RangeToLspRange
  ``(Block.other
      (Block.multilean
        $(← wpQuoteHighlight hls)
        $(quote placeholders)
        (some $(quote (← getFileName)))
        $(quote range))
      #[$content,*])

/--
Custom `multilean` directive that extends the upstream Verso implementation to
treat `:::input` blocks specially: lean code inside an `:::input` block is
included in the combined source that gets elaborated (so it can contribute to
type-checking), while the first line of the block is still replaced with the
placeholder marker so that `splitMultileanCode` correctly demarcates the
boundary for display purposes.
-/
@[directive]
def multilean : DirectiveExpanderOf LeanBlockConfig
  | config, blocks => do
    let sourceText := (← getFileMap).source
    let mut source := ""
    let mut lastPos : String.Pos.Raw := 0
    let mut placeholders : Array ExplanationPlaceholder := #[]
    let mut explanationBlocks : Array Term := #[]
    let mut leanBodies : Array StrLit := #[]
    for block in blocks do
      match block with
      -- Direct lean code block inside ::::multilean
      | `(block|``` $nameStx:ident $argsStx* | $contents:str ```) =>
        if nameStx.getId == `lean then
          let start := contents.raw.getPos?.getD lastPos
          source := source ++ wpBlankOfSameShape (lastPos.extract sourceText start)
          let stop := contents.raw.getTailPos?.getD start
          if argsStx.size != 0 then
            throwErrorAt nameStx "Lean blocks inside `:::multilean` do not support per-block arguments"
          source := source ++ (start.extract sourceText stop)
          leanBodies := leanBodies.push contents
          lastPos := stop
        else
          let start := block.raw.getPos?.getD lastPos
          source := source ++ wpBlankOfSameShape (lastPos.extract sourceText start)
          let stop := block.raw.getTrailingTailPos?.getD start
          let (placeholder, masked) := wpExplanationPlaceholderSource placeholders.size (start.extract sourceText stop)
          source := source ++ masked
          placeholders := placeholders.push placeholder
          explanationBlocks := explanationBlocks.push (← elabBlock block)
          lastPos := stop
      -- :::input directive block: preserve lean code for elaboration, use
      -- first line as placeholder marker for display splitting.
      | `(block|::: $name $_args* { $innerBlocks* }) =>
        if name.raw.getId == `input then
          let blockStart := block.raw.getPos?.getD lastPos
          source := source ++ wpBlankOfSameShape (lastPos.extract sourceText blockStart)
          let blockStop := block.raw.getTrailingTailPos?.getD blockStart
          let (placeholder, inputSrc) :=
            inputBlockSource placeholders.size sourceText blockStart blockStop innerBlocks
          source := source ++ inputSrc
          placeholders := placeholders.push placeholder
          explanationBlocks := explanationBlocks.push (← elabBlock block)
          -- Track inner lean bodies so warnLongLines applies to them too.
          for ib in innerBlocks do
            if let `(block|``` $n:ident $_iba* | $c:str ```) := ib then
              if n.getId == `lean then leanBodies := leanBodies.push c
          lastPos := blockStop
        else
          -- Other directives: treat as opaque explanation blocks.
          let start := block.raw.getPos?.getD lastPos
          source := source ++ wpBlankOfSameShape (lastPos.extract sourceText start)
          let stop := block.raw.getTrailingTailPos?.getD start
          let (placeholder, masked) := wpExplanationPlaceholderSource placeholders.size (start.extract sourceText stop)
          source := source ++ masked
          placeholders := placeholders.push placeholder
          explanationBlocks := explanationBlocks.push (← elabBlock block)
          lastPos := stop
      -- All other blocks (prose, headings, …): opaque explanation blocks.
      | other =>
        let start := other.raw.getPos?.getD lastPos
        source := source ++ wpBlankOfSameShape (lastPos.extract sourceText start)
        let stop := other.raw.getTrailingTailPos?.getD start
        let (placeholder, masked) := wpExplanationPlaceholderSource placeholders.size (start.extract sourceText stop)
        source := source ++ masked
        placeholders := placeholders.push placeholder
        explanationBlocks := explanationBlocks.push (← elabBlock other)
        lastPos := stop
    if leanBodies.isEmpty then
      throwErrorAt (← getRef) "`:::multilean` requires at least one ```lean``` block"
    for body in leanBodies do
      if config.show then
        let col? := body.raw.getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)
        warnLongLines col? body
    elabCommandsCore config source (← getRef) source
      (wpToHighlightedMultileanBlock placeholders explanationBlocks)

end WaterproofGenre
