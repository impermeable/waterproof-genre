import Lake
open Lake DSL

require «verso» from git "https://github.com/leanprover/verso.git"@"main"

package "WaterproofGenre" where
  version := v!"0.1.0"

@[default_target]
lean_lib WaterproofGenre where
  roots := #[`WaterproofGenre]

@[default_target]
lean_exe "waterproofgenre" where
  root := `WaterproofGenreMain
