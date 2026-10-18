import Math.RepresentationTheory.CovariantCharacterObstruction
import TauCeti.RepresentationTheory.FDRep

/-! Covariant dual-index compatibility and the ambiguity of full spectra. -/
namespace Math.DualIndexCompatibility
set_option autoImplicit false
noncomputable section
open Representation AutomorphismCovariantHom
variable {k G H V : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (a : Representation k G V)

/-- An added gauge singlet is invisible to the dual index. -/
def withSinglet := a.prod (trivial k G k)

theorem withSinglet_dual_index (g : G) :
    (withSinglet a).character g - (withSinglet a).dual.character g =
      a.character g - a.dual.character g := by
  simp only [withSinglet, char_dual, char_prod, char_trivial, Module.finrank_self]
  abel

theorem withSinglet_character_ne (g : G) :
    (withSinglet a).character g ≠ a.character g := by
  simp [withSinglet, char_prod, char_trivial]

/-- Identical dual index does not imply an equivalence of full representations. -/
theorem withSinglet_not_equiv : ¬ Nonempty (Representation.Equiv a (withSinglet a)) := by
  rintro ⟨e⟩
  exact withSinglet_character_ne a 1 (congrFun (char_iso e) 1).symm

/-- A charged vectorlike pair is also invisible to the dual index. -/
def withVectorlike := a.prod (a.prod a.dual)

theorem withVectorlike_dual_index (g : G) :
    (withVectorlike a).character g - (withVectorlike a).dual.character g =
      a.character g - a.dual.character g := by
  simp only [withVectorlike, char_dual, char_prod, inv_inv]
  abel

variable (alpha : H →* MulAut G) (A : Action a alpha)
include A

theorem dual_index_invariant (h : H) (g : G) :
    a.character (alpha h g) - a.dual.character (alpha h g) =
      a.character g - a.dual.character g := by
  simp only [char_dual, ← map_inv,
    CovariantCharacterObstruction.character_invariant a alpha A]
end
end Math.DualIndexCompatibility
