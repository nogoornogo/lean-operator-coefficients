import Lake
open Lake DSL

package «operator-completeness» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "1a547d8a48a8fa7877d2decb69d7294723bb0187"

require TauCeti from git
  "https://github.com/TauCetiProject/TauCeti.git" @
    "b9e2e182804073eb92718b68a9baf37df8e189bd"

lean_lib Math where

lean_lib Physics where

@[default_target]
lean_lib GUT where
