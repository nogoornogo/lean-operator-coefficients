import Math.RepresentationTheory.Jets.GradedJetIBP
import Math.RepresentationTheory.Tensors.ExternalInvariantTensor

/-! Currents carry the direction representation as well as the field action.
The relation is the actual divergence range; no ideal closure is taken. -/
namespace Math.CovariantJetIBP
set_option autoImplicit false
noncomputable section
open scoped TensorProduct

variable {I : Type*} {V : ℕ → Type*}
  [∀ d, AddCommGroup (V d)] [∀ d, Module ℂ (V d)]
  (D : ∀ _i : I, ∀ d, V d →ₗ[ℂ] V (d + 1))

abbrev Current (I : Type*) (V : ℕ → Type*)
    [∀ d, AddCommGroup (V d)] [∀ d, Module ℂ (V d)] (d : ℕ) :=
  (I →₀ ℂ) ⊗[ℂ] V d

def divergence (d : ℕ) : Current I V d →ₗ[ℂ] V (d + 1) :=
  TensorProduct.lift (Finsupp.linearCombination ℂ (fun i => D i d))

@[simp] theorem divergence_single (d : ℕ) (i : I) (p : V d) :
    divergence D d (Finsupp.single i 1 ⊗ₜ[ℂ] p) = D i d p := by simp [divergence]

def relations (d : ℕ) : Submodule ℂ (V (d + 1)) := (divergence D d).range

theorem derivative_mem (d : ℕ) (i : I) (p : V d) : D i d p ∈ relations D d :=
  ⟨Finsupp.single i 1 ⊗ₜ[ℂ] p, divergence_single D d i p⟩

theorem relations_eq (d : ℕ) : relations D d = GradedJetIBP.relations D d := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    induction c using TensorProduct.inductionOn with
    | add c e hc he => simpa only [map_add] using Submodule.add_mem _ hc he
    | tmul v p =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v w hv hw => simpa only [TensorProduct.add_tmul, map_add] using Submodule.add_mem _ hv hw
      | single i c =>
        rw [show Finsupp.single i c = c • Finsupp.single i (1 : ℂ) by simp,
          ← TensorProduct.smul_tmul', map_smul, divergence_single]
        exact Submodule.smul_mem _ _ (GradedJetIBP.derivative_mem D d i p)
  · rintro _ ⟨c, rfl⟩
    induction c using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using (relations D d).zero_mem
    | add c e hc he => simpa only [map_add] using (relations D d).add_mem hc he
    | single i p => simpa only [GradedJetIBP.divergence_single] using derivative_mem D d i p

theorem annihilates_iff {W : Type*} [AddCommGroup W] [Module ℂ W] (d : ℕ)
    (f : V (d + 1) →ₗ[ℂ] W) :
    relations D d ≤ f.ker ↔ ∀ i p, f (D i d p) = 0 := by
  rw [relations_eq]; exact GradedJetIBP.annihilates_iff D d f

variable [Fintype I] {H : Type*} [Group H]
  (σ : Representation ℂ H (I →₀ ℂ)) (ρ : ∀ d, Representation ℂ H (V d))
  (cov : ∀ h i d p, ρ (d + 1) h (D i d p) =
    ∑ j, (σ h (Finsupp.single i 1)) j • D j d (ρ d h p))

def currentAction (d : ℕ) : Representation ℂ H (Current I V d) := σ.tprod (ρ d)

theorem divergence_tmul (d : ℕ) (v : I →₀ ℂ) (p : V d) :
    divergence D d (v ⊗ₜ[ℂ] p) = ∑ i, v i • D i d p := by
  change (v.sum (fun i c => c • D i d)) p = _
  rw [Finsupp.sum_fintype v (fun i c => c • D i d) (fun _ => zero_smul _ _)]
  simp

include cov in
theorem divergence_covariant (d : ℕ) (h : H) (c : Current I V d) :
    ρ (d + 1) h (divergence D d c) = divergence D d (currentAction σ ρ d h c) := by
  induction c using TensorProduct.inductionOn with
  | add c e hc he => simp only [map_add, hc, he]
  | tmul v p =>
    change ρ (d + 1) h (divergence D d (v ⊗ₜ[ℂ] p)) =
      divergence D d (σ h v ⊗ₜ[ℂ] ρ d h p)
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add, TensorProduct.add_tmul, hv, hw]
    | single i c =>
      rw [show Finsupp.single i c = c • Finsupp.single i (1 : ℂ) by simp]
      rw [← TensorProduct.smul_tmul', map_smul, map_smul, map_smul,
        ← TensorProduct.smul_tmul', map_smul, divergence_single, cov h i d p,
        divergence_tmul]

include cov in
theorem stable (d : ℕ) :
    ∀ h, relations D d ≤ (relations D d).comap (ρ (d + 1) h) := by
  rintro h _ ⟨c, rfl⟩
  exact ⟨currentAction σ ρ d h c, (divergence_covariant D σ ρ cov d h c).symm⟩

abbrev quotient (d : ℕ) := (ρ (d + 1)).quotient (relations D d) (stable D σ ρ cov d)
abbrev Coefficient (d : ℕ) := RelationQuotient.vanishing
  (ρ (d + 1)) (Representation.trivial ℂ H ℂ) (relations D d)

def coefficientEquiv (d : ℕ) : Coefficient D ρ d ≃ₗ[ℂ]
    Representation.IntertwiningMap (quotient D σ ρ cov d) (Representation.trivial ℂ H ℂ) :=
  RelationQuotient.equiv _ _ _ (stable D σ ρ cov d)

@[simp] theorem coefficientEquiv_mk (d : ℕ) (f : Coefficient D ρ d) (p : V (d + 1)) :
    coefficientEquiv D σ ρ cov d f ((relations D d).mkQ p) = f.val p := rfl

@[simp] theorem coefficientEquiv_symm (d : ℕ)
    (f : Representation.IntertwiningMap (quotient D σ ρ cov d) (Representation.trivial ℂ H ℂ))
    (p : V (d + 1)) : ((coefficientEquiv D σ ρ cov d).symm f).val p =
      f ((relations D d).mkQ p) := rfl

end
end Math.CovariantJetIBP
