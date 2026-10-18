import Math.RepresentationTheory.Decomposition.IrreducibleHomScalar

namespace Math.ScalarIrreducible
set_option autoImplicit false
noncomputable section
open Representation
variable {G : Type*} [Group G]

theorem irreducible (r : Representation ℂ G ℂ) : IsIrreducible r := by
  have : Nontrivial (Subrepresentation r) := ⟨⟨⊥,⊤,by
    intro h
    have hh := congrArg Subrepresentation.toSubmodule h
    exact (bot_ne_top : (⊥ : Submodule ℂ ℂ) ≠ ⊤) hh⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hs
  rcases eq_bot_or_eq_top S.toSubmodule with h | h
  · exact False.elim (hs (Subrepresentation.toSubmodule_injective h))
  · exact Subrepresentation.toSubmodule_injective h
end
end Math.ScalarIrreducible
