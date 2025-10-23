-- This module serves as the root of the `WaterproofGenre` library.
-- Import modules here that should be built as part of the library.
-- import WaterproofGenre.Demo

import Verso
import VersoManual

open Verso Doc

-- make inline Lean blocks available to the users of this genre
export Verso.Genre.Manual.InlineLean (lean)

abbrev Block := Genre.Manual.Block

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
