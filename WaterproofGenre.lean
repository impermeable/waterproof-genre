-- This module serves as the root of the `WaterproofGenre` library.
-- Import modules here that should be built as part of the library.
-- import WaterproofGenre.Demo

import Verso
import Lean.Elab
import SubVerso.Highlighting
import Init.Data.ToString.Basic
import Verso.Code
import WaterproofGenre.GoalWidget

open Verso Doc
open Lean (Name Json NameMap ToJson FromJson)
open Lean Elab
open Verso ArgParse Html Code

open Verso.Doc Elab
open Lean.Quote
open Lean Syntax

open SubVerso.Highlighting

structure Block where
  name : Name
  id : String

structure HintConfig where
  title : String

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
def lean : CodeBlockExpander
  | _, str => do
    let altStr ← parserInputString str
    processString altStr

def Block.hint : Block where
  name := `Block.hint
  id := "hint"

@[directive_expander hint]
def hint : DirectiveExpander
  | args, contents => do
    let title ←  ArgParse.run ((some <$> .positional `title .string) <|> pure none) args
    let blocks ← contents.mapM elabBlock
    let val ← ``(Block.other Block.hint  #[ $blocks ,* ])
    pure #[val]


def Block.multilean : Block where
  name := `Block.multilean
  id := "Multilean"

partial def extractString (stxs : Array Syntax) (start : String.Pos := String.Pos.mk 0) : DocElabM (String × String.Pos):= do
  let mut code := ""
  let mut lastIdx := start

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
    let val ← processString str
    -- let args ← stxs.mapM elabBlocko
    -- Note that we do not actually pass any of the content here
    -- To produce output, this would be needed.
    let val ← ``(Block.other Block.multilean #[])
    pure #[val]
  | _, _ => Lean.Elab.throwUnsupportedSyntax

def Block.input : Block where
  name := `Block.input
  id := "input"

@[directive_expander input]
def input : DirectiveExpander
  | #[], stxs => do
    let args ← stxs.mapM elabBlock
    let val ← ``(Block.other Block.input #[ $[ $args ],* ])
    pure #[val]
  | _, _ => Lean.Elab.throwUnsupportedSyntax

def WaterproofGenre : Genre where
  Inline := Empty
  Block := Block
  PartMetadata := Unit
  TraverseContext := Unit
  TraverseState := Unit
