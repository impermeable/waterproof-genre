import Lake
open Lake DSL

require «verso» from git "https://github.com/ejgallego/verso.git"@"4e64c2df6ef2267fc1d613f7f0cd4e4c00742f6a"
require «proofwidgets» from git "https://github.com/leanprover-community/ProofWidgets4"@"v0.0.90"

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
