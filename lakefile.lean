import Lake
open Lake DSL

package sideLvConservation where
  leanOptions := #[]

-- Mathlib pinned to match the working pin used by SIDE-grh-transfer
-- (Lean v4.29.1 + Mathlib commit 5e932f9). Federation discipline: no
-- Lake cross-dependencies on sister kernels; Mathlib is the sole source
-- of imported content.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

@[default_target]
lean_lib SIDELvConservation where
  srcDir := "."
  globs := #[.submodules `SIDELvConservation]
