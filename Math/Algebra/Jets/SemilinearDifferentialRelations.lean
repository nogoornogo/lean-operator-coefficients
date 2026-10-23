import Math.Algebra.Jets.TwoSidedDifferentialRelations
import Mathlib.Algebra.Star.Module

/-! Conjugation descends through full EOM and linear IBP relations.
This quotient is used only as a module. -/
namespace Math.SemilinearDifferentialRelations
set_option autoImplicit false
noncomputable section
variable {A I : Type*} [Ring A] [Algebra ℂ A]
  (D : I → A →ₗ[ℂ] A) (R : Set A) (j : A →ₛₗ[starRingEnd ℂ] A)
  (hM : ∀ p q, j (p*q) = j p*j q)
  (hD : ∀ i p, j (D i p) = D i (j p))
  (hR : ∀ p ∈ R, j p ∈ TwoSidedDifferential.relations D R)

include hM hD hR in
theorem equations {p : A} (hp : p ∈ TwoSidedDifferential.relations D R) :
    j p ∈ TwoSidedDifferential.relations D R := by
  induction hp with
  | seed p hp => exact hR p hp
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add hp hq ihp ihq => rw [map_add]; exact Submodule.add_mem _ ihp ihq
  | smul c hp ih => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ ih
  | left a hp ih => rw [hM]; exact TwoSidedDifferential.left_mem _ _ _ ih
  | right a hp ih => rw [hM]; exact TwoSidedDifferential.right_mem _ _ _ ih
  | derivative i hp ih => rw [hD]; exact TwoSidedDifferential.derivative_mem _ _ i ih

include hD in
theorem ibp {p : A} (hp : p ∈ (VariationalIBP.divergence D).range) :
    j p ∈ (VariationalIBP.divergence D).range := by
  obtain ⟨v,rfl⟩ := hp
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
  | single i p =>
    rw [VariationalIBP.divergence_single,hD]
    exact ⟨Finsupp.single i (j p),VariationalIBP.divergence_single _ _ _⟩

include hM hD hR in
theorem stable : TwoSidedDifferential.combined D R ≤
    (TwoSidedDifferential.combined D R).comap j := by
  apply sup_le
  · intro p hp
    exact Submodule.mem_sup_left (equations D R j hM hD hR hp)
  · intro p hp
    exact Submodule.mem_sup_right (ibp D j hD hp)

def quotient : (A ⧸ TwoSidedDifferential.combined D R) →ₛₗ[starRingEnd ℂ]
    (A ⧸ TwoSidedDifferential.combined D R) :=
  (TwoSidedDifferential.combined D R).mapQ _ j (stable D R j hM hD hR)

@[simp] theorem quotient_mk (p : A) :
    quotient D R j hM hD hR ((TwoSidedDifferential.combined D R).mkQ p) =
      (TwoSidedDifferential.combined D R).mkQ (j p) := rfl

theorem quotient_involutive (hj : ∀ p, j (j p) = p)
    (x : A ⧸ TwoSidedDifferential.combined D R) :
    quotient D R j hM hD hR (quotient D R j hM hD hR x) = x := by
  obtain ⟨p,rfl⟩ := (TwoSidedDifferential.combined D R).mkQ_surjective x
  rw [quotient_mk,quotient_mk,hj]
end
end Math.SemilinearDifferentialRelations
