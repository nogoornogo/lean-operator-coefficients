import TauCeti.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Irreducibility under contragredients and enlargement of the acting group.
No compactness or finite-group assumption is needed. -/

namespace Math.RepresentationTheory
noncomputable section
open Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

theorem isIrreducible_of_comp {H : Type*} [Group H]
    (rho : Representation k G V) (f : H →* G)
    [IsIrreducible (rho.comp f)] : IsIrreducible rho := by
  let : Nontrivial V := IsIrreducible.nontrivial (ρ := rho.comp f) inferInstance
  let : Nontrivial (Subrepresentation rho) :=
    ⟨⟨⊥, ⊤, fun h => (bot_ne_top : (⊥ : Submodule k V) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule h)⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  let T : Subrepresentation (rho.comp f) :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule h := S.apply_mem_toSubmodule (f h) }
  rcases eq_bot_or_eq_top T with h | h
  · have hc : T.toSubmodule = (⊥ : Submodule k V) :=
      congrArg Subrepresentation.toSubmodule h
    exact (hS (Subrepresentation.toSubmodule_injective hc)).elim
  · have hc : T.toSubmodule = (⊤ : Submodule k V) :=
      congrArg Subrepresentation.toSubmodule h
    exact Subrepresentation.toSubmodule_injective hc

def coannihilator (rho : Representation k G V) (S : Subrepresentation rho.dual) :
    Subrepresentation rho where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g := by
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro phi hphi
    have h := hv (rho.dual g⁻¹ phi) (S.apply_mem_toSubmodule g⁻¹ hphi)
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h

theorem dual_isIrreducible (rho : Representation k G V)
    [FiniteDimensional k V] [IsIrreducible rho] : IsIrreducible rho.dual := by
  let : Nontrivial V := IsIrreducible.nontrivial (ρ := rho) inferInstance
  let : Nontrivial (Subrepresentation rho.dual) :=
    ⟨⟨⊥, ⊤, fun h => (bot_ne_top : (⊥ : Submodule k (Module.Dual k V)) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule h)⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hd := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule)
  rcases eq_bot_or_eq_top (coannihilator rho S) with h | h
  · have hc : S.toSubmodule.dualCoannihilator = ⊥ :=
      congrArg Subrepresentation.toSubmodule h
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, hc, Submodule.dualAnnihilator_bot]
    rfl
  · have hc : S.toSubmodule.dualCoannihilator = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    exfalso
    apply hS
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, hc, Submodule.dualAnnihilator_top]
    rfl

end
end Math.RepresentationTheory
