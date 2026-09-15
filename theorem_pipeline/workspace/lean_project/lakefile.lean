import Lake
open Lake DSL

package "ProofWorkspace"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "8f9d9cff6bd728b17a24e163c9402775d9e6a365"

@[default_target]
lean_lib "ProofWorkspace" where
  -- Resource-only setting for deep kernel reduction of the finite source stream.
  -- Weak arguments do not invalidate unchanged proof build traces.
  weakLeanArgs := #["-s", "131072"]
