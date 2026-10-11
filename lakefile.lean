import Lake
open Lake DSL

package «lehner-edges» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"
require «lean-sudakov» from git
  "https://github.com/T1mberland/Lean-Sudakov.git" @ "bcd86db77e0153159977b8085f7ffdd993a3d3e9"
require «lean-log-sobolev» from git
  "https://github.com/T1mberland/lean-log-sobolev.git" @ "1a95157e7d4cc18d444aa640c751acbe4c7692d4"

@[default_target]
lean_lib LehnerEdges where

-- Both external libraries export a different `map_update_prod_pi` globally.
-- Rename only Sudakov's declaration and its use; no mathematical code changes.
post_update pkg do
  let sourceFile := pkg.dir / ".lake" / "packages" / "lean-sudakov" /
    "LeanSudakov" / "GaussianVectorIBP.lean"
  let source ← IO.FS.readFile sourceFile
  if (source.splitOn "theorem map_update_prod_pi").length > 1 then
    IO.FS.writeFile sourceFile
      (source.replace "map_update_prod_pi" "LehnerSudakovCompat.map_update_prod_pi")
