-- This module serves as the root of the `WaterproofGenre` library.
-- Import modules here that should be built as part of the library.
-- import WaterproofGenre.Demo

import Verso
import Lean.Elab
import Verso.Doc
import SubVerso.Examples.Slice
import SubVerso.Highlighting
import Init.Data.ToString.Basic
import Verso.Code

open Verso Doc
open Lean (Name Json NameMap ToJson FromJson)
open Lean Elab
open Verso ArgParse Html Code

open Verso.Doc Elab
open Lean.Quote
open Lean Syntax

open SubVerso.Examples.Slice
open SubVerso.Highlighting

-- make inline Lean blocks available to the users of this genre

structure Block where
  name : Name
  id : String

structure HintConfig where
  title : String


------

def parserInputString [Monad m] [MonadFileMap m] (str : TSyntax `str) : m String := do
  let preString := (← getFileMap).source.extract 0 (str.raw.getPos?.getD 0)
  let mut code := ""
  let mut iter := preString.iter
  while !iter.atEnd do
    if iter.curr == '\n' then code := code.push '\n'
    else
      for _ in [0:iter.curr.utf8Size] do
        code := code.push ' '
    iter := iter.next
  code := code ++ str.getString
  return code

def processString (altStr : String) :  DocElabM (Array (TSyntax `term)) := do
  dbg_trace "Processing {altStr}"
  let ictx := Parser.mkInputContext altStr (← getFileName)
  let cctx : Command.Context := { fileName := ← getFileName, fileMap := FileMap.ofString altStr, cancelTk? := none, snap? := none}
  let mut cmdState : Command.State := {env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes := [{header := ""}, {header := ""}]}
  let mut pstate := {pos := 0, recovering := false}
  let mut exercises := #[]
  let mut solutions := #[]

  repeat
    let scope := cmdState.scopes.head!
    let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmd, ps', messages) := Parser.parseCommand ictx pmctx pstate cmdState.messages
    pstate := ps'
    cmdState := {cmdState with messages := messages}

    -- dbg_trace "Unsliced is {cmd}"
    let slices : Slices ← DocElabM.withFileMap (FileMap.ofString altStr) (sliceSyntax cmd)
    let sol := slices.sliced.getD "solution" slices.residual
    solutions := solutions.push sol

    cmdState ← withInfoTreeContext (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `DemoTextbook.Exts.lean, stx := cmd})) do
      let mut cmdState := cmdState
      match (← liftM <| EIO.toIO' <| (Command.elabCommand sol cctx).run cmdState) with
      | Except.error e => logError e.toMessageData
      | Except.ok ((), s) =>
        cmdState := s

      pure cmdState

    if Parser.isTerminalCommand cmd then break

  setEnv cmdState.env
  for t in cmdState.infoState.trees do
    -- dbg_trace (← t.format)
    pushInfoTree t

  for msg in cmdState.messages.msgs do
    logMessage msg

  let mut hls := Highlighted.empty
  for cmd in exercises do
    hls := hls ++ (← highlight cmd cmdState.messages.msgs.toArray cmdState.infoState.trees)

  pure #[]


@[code_block_expander lean]
def lean: CodeBlockExpander
  | _, str => do
    let altStr ← parserInputString str
    processString altStr

def Block.hint (title : String): Block where
  name := `Block.hint
  id := "hint"
-----------

-- Multilean

def Block.multilean : Block where
  name := `Block.multilean
  id := "Multilean"

def extractString (stxs : Array Syntax) : DocElabM (String) := do
  let mut code := ""
  let mut lastIdx := 0
  for stx in stxs do
    match stx with
    | `(block|``` $_nameStx:ident $_argsStx* | $contents:str ```) => do
      let preString := (← getFileMap).source.extract lastIdx (contents.raw.getPos?.getD 0)
      let mut iter := preString.iter
      while !iter.atEnd do
        if iter.curr == '\n' then
          code := code.push '\n'
        else
          for _ in [0:iter.curr.utf8Size] do
            code := code.push ' '
        iter := iter.next

      lastIdx := contents.raw.getTailPos?.getD lastIdx
      code := (code ++ contents.getString)
    | _ => pure ()
  pure code

@[directive_expander multilean]
def multilean : DirectiveExpander
  | #[], stxs => do
    let str ← extractString stxs
    let val ← processString str
    -- let args ← stxs.mapM elabBlocko
    -- Note that we do not actually pass any of the content here
    -- To produce output, this would be needed.
    let val ← ``(Block.other Block.multilean #[])
    pure #[val]
  | _, _ => Lean.Elab.throwUnsupportedSyntax


-- End Multilean

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m]


def HintConfig.parse : ArgParse m HintConfig :=
  HintConfig.mk <$> .positional `title .string

instance : FromArgs HintConfig m := ⟨HintConfig.parse⟩

end

@[directive]
def hint : DirectiveExpanderOf HintConfig
  | cfg, contents => do
      let blocks ← contents.mapM elabBlock
      ``(Block.other (Block.hint $(quote cfg.title)) #[ $blocks ,* ])


def WaterproofGenre : Genre where
  Inline := Empty
  -- Block := Block.lean
  Block := Block
  PartMetadata := Unit
  TraverseContext := Unit
  TraverseState := Unit

namespace WaterproofGenre

open Verso.Output Html

instance : TraversePart WaterproofGenre := {}
instance : TraverseBlock WaterproofGenre := {}

abbrev TraverseM := ReaderT WaterproofGenre.TraverseContext (StateT Unit Id)

instance : Traverse WaterproofGenre TraverseM where
  part _ := pure none
  block _ := pure ()
  inline _ := pure ()
  genrePart _ _ := pure none
  genreBlock _ _ := do pure none
  genreInline _ _ := pure none

instance : GenreHtml WaterproofGenre IO where
  -- part recur metadata p := pure {{<span>{{"hello"}}</span>}}
  part recur metadata
    | .mk title titleString _ content subParts =>
        recur (.mk title titleString none content subParts)
  block inlineToHtml recur blkExt blocks := blocks.mapM recur
  inline _ i := nomatch i

def render (doc : Part WaterproofGenre) : IO UInt32 := do
  let hadError ← IO.mkRef false
  let logError str := do
    hadError.set true
    IO.eprintln str

  let (content, _) ← WaterproofGenre.toHtml {logError} () () {} {} {} doc .empty
  let html := {{
    <html>
      <head>
        <title>{{ doc.titleString }}</title>
        <meta charset="utf-8"/>
      </head>
      <body>{{ content }}</body>
    </html>
  }}

  IO.println "Writing to index.html"
  IO.FS.withFile "index.html" .write fun h => do
    h.putStrLn html.asString

  if (← hadError.get) then
    IO.eprintln "Errors occurred while rendering"
    pure 1
  else
    pure 0

end WaterproofGenre
