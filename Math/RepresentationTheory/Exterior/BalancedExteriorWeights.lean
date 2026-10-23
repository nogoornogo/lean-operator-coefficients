import TauCeti.LinearAlgebra.ExteriorPower.Basis
import Math.RepresentationTheory.Weights.BoundedTorusWeights
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-! Pauli capacity sharpens the weak weight bound at complementary degrees. -/
namespace Math.BalancedExteriorWeights
set_option autoImplicit false
noncomputable section
open Representation BoundedTorusWeights

theorem subset_bound {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → ℤ) (hw : ∀ i, -1 ≤ w i ∧ w i ≤ 1) (hz : ∑ i, w i = 0)
    (s : Finset I) :
    -((min s.card (Fintype.card I-s.card) : ℕ) : ℤ) ≤ ∑ i ∈ s, w i ∧
      (∑ i ∈ s, w i) ≤ ((min s.card (Fintype.card I-s.card) : ℕ) : ℤ) := by
  have hcard : s.card ≤ Fintype.card I := Finset.card_le_univ s
  have hb (t : Finset I) : -(t.card : ℤ) ≤ ∑ i ∈ t, w i ∧
      (∑ i ∈ t, w i) ≤ (t.card : ℤ) := by
    constructor
    · calc
        _ = ∑ _i ∈ t, (-1 : ℤ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => (hw i).1
    · calc
        _ ≤ ∑ _i ∈ t, (1 : ℤ) := Finset.sum_le_sum fun i _ => (hw i).2
        _ = _ := by simp
  have hc := hb sᶜ
  have hs := hb s
  have he : (∑ i ∈ s, w i) + ∑ i ∈ sᶜ, w i = 0 := by
    rw [Finset.sum_add_sum_compl, hz]
  rw [Finset.card_compl, Nat.cast_sub hcard] at hc
  rw [Nat.cast_min, Nat.cast_sub hcard]
  constructor <;> omega

variable {G V I : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [Fintype I] [DecidableEq I] [LinearOrder I]

theorem bounded (rho : Representation ℂ G V) (torus : Circle →* G)
    (b : Module.Basis I ℂ V) (w : I → ℤ)
    (he : ∀ i, Eigen rho torus (w i) (b i))
    (hw : ∀ i, -1 ≤ w i ∧ w i ≤ 1) (hz : ∑ i, w i = 0) (n : ℕ) :
    Bounded (rho.exteriorPower n) torus (min n (Fintype.card I-n)) := by
  apply of_basis _ _ (b.exteriorPower n) (fun s => ∑ i ∈ s.val, w i) _
  · intro s z
    rw [Representation.exteriorPower_apply,
      Module.Basis.map_exteriorPower_of_apply b (rho (torus z))
        (fun i => (z : ℂ)^w i) (fun i => he i z)]
    congr 1
    have hp (t : Finset I) : (∏ i ∈ t, (z : ℂ)^w i) = (z : ℂ)^(∑ i ∈ t, w i) := by
      induction t using Finset.induction_on with
      | empty => simp
      | @insert i t hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ z.coe_ne_zero]
    exact hp s.val
  · intro s
    simpa only [Set.powersetCard.mem_iff.mp s.property] using subset_bound w hw hz s.val

end
end Math.BalancedExteriorWeights
