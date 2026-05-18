import Lake
open Lake DSL

require «verso» from git "https://github.com/pimotte/verso"@"error-option-fix"

meta if get_config? env != some "dev" then
  require «proofwidgets» from git "https://github.com/leanprover-community/ProofWidgets4"@"v0.0.90"

meta if get_config? env = some "dev" then
  require «verbose-lean4» from git "https://github.com/impermeable/verbose-lean4"@"update/v4.29.0-rc6"

package "WaterproofGenre" where
  version := v!"0.1.0"

@[default_target]
lean_lib WaterproofGenre where
  roots := #[`WaterproofGenre]

@[default_target]
lean_exe "waterproofgenre" where
  root := `WaterproofGenreMain

lean_lib WaterproofGenreVerbose where
  roots := #[`WaterproofGenre.Verbose]

lean_exe "test-demo" where
  root := `TestDemoMain
