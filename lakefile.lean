import Lake
open Lake DSL

package «operator-completeness» where
  -- Runtime scheduling only: keep proof options and dependency traces unchanged.
  weakLeanArgs := #["-j2"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "074063781836922cb02701cd12943c9f51731afa"

require TauCeti from git
  "https://github.com/TauCetiProject/TauCeti.git" @
    "1f9b4414105d86e487a4ac4c3d3397076a44d0d2"

require Physlib from git
  "https://github.com/leanprover-community/physlib.git" @
    "5bbbb30d08b8e151406a10affbc8a369b74b32c6"

lean_lib Math where

lean_lib Physics where

@[default_target]
lean_lib GUT where
