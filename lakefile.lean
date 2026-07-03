import Lake
open Lake DSL

package «OSPositivity» where
  -- Satellite repository for lattice reflection positivity and OS interfaces.

lean_lib «OSPositivity» where
  -- Public root: OSPositivity.lean

lean_lib «Interfaces» where
  -- Contract root imported by the mother repository.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "07642720480157414db592fa85b626dafb71355b"
