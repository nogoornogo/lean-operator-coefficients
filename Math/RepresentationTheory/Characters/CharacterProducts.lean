import Mathlib.RepresentationTheory.Character
import Mathlib.Basic.Complex.Basic

namespace Math.CharacterProducts
noncomputable section
open Representation
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem prod_character (a : Representation ℂ G V) (b : Representation ℂ G W) (g : G) :
    (a.prod b).character g = a.character g + b.character g :=
  LinearMap.trace_prodMap' (a g) (b g)
end
end Math.CharacterProducts
