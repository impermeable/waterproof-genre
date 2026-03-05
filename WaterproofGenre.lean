-- This module serves as the root of the `WaterproofGenre` library.
-- Import modules here that should be built as part of the library.
-- import WaterproofGenre.Demo

import Verso
import Lean.Elab
import Lean.DocString.Syntax
import SubVerso.Highlighting
import Init.Data.ToString.Basic
import Verso.Code
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
