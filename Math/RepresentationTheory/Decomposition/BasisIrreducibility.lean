import Mathlib.RepresentationTheory.Irreducible

/-! A coordinate criterion for irreducibility, independent of a particular group. -/

set_option autoImplicit false

namespace Math.RepresentationTheory

theorem irreducible_of_basis_coordinates
    {k G V I : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    [Nontrivial V] [Fintype I] (rho : Representation k G V) (b : Module.Basis I k V)
    (hproject : ∀ (S : Subrepresentation rho) (v : V), v ∈ S →
      ∀ i, b.repr v i • b i ∈ S)
    (hmix : ∀ i j, ∃ g, b.repr (rho g (b i)) j ≠ 0) :
    rho.IsIrreducible := by
  classical
  let : Nontrivial (Subrepresentation rho) :=
    ⟨⟨⊥, ⊤, fun h => (bot_ne_top : (⊥ : Submodule k V) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule h)⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hSub : S.toSubmodule ≠ ⊥ := by
    intro h
    exact hS (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSub
  obtain ⟨i, hi⟩ : ∃ i, b.repr v i ≠ 0 := by
    by_contra! h
    apply hv0
    apply b.repr.injective
    ext i
    simp [h]
  have extract (w : V) (hw : w ∈ S) (j : I) (hj : b.repr w j ≠ 0) : b j ∈ S := by
    change b j ∈ S.toSubmodule
    have := S.toSubmodule.smul_mem (b.repr w j)⁻¹ (hproject S w hw j)
    simpa [smul_smul, hj] using this
  have hiS := extract v hv i hi
  have hb (j : I) : b j ∈ S := by
    obtain ⟨g, hg⟩ := hmix i j
    exact extract _ (S.apply_mem_toSubmodule g hiS) j hg
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro w _
  rw [← b.sum_repr w]
  exact S.toSubmodule.sum_mem fun j _ => S.toSubmodule.smul_mem _ (hb j)

end Math.RepresentationTheory
