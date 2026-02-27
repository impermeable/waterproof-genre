import Lake
open Lake DSL

require «verso» from git "https://github.com/leanprover/verso.git"@"v4.25.0"
require «proofwidgets» from git "https://github.com/leanprover-community/ProofWidgets4"@"v0.0.79"

package "WaterproofGenre" where
  version := v!"0.1.0"

@[default_target]
lean_lib WaterproofGenre where
  roots := #[`WaterproofGenre]

@[default_target]
lean_exe "waterproofgenre" where
  root := `WaterproofGenreMain

lean_exe "test-demo" where
  root := `TestDemoMain
