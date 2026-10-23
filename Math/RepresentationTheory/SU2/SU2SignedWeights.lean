import Math.RepresentationTheory.SU2.SU2CoefficientExtraction

/-! Finite signed-weight expansions yield a structural A1 × A1 extraction
formula, with degrees kept symbolic. -/
namespace Math.SU2SignedWeights
set_option autoImplicit false
noncomputable section
open TauCeti MeasureTheory SU2WeightExtraction
open scoped BigOperators

def normalization (k : ℤ) : ℂ := if k = 0 then 1 else 1/2

theorem signed_pair (k : ℤ) (z : Circle) :
    ((z : ℂ)^k + ((z⁻¹ : Circle) : ℂ)^k) / 2 =
      normalization k * pairWeight k.natAbs z := by
  cases k with
  | ofNat n =>
    change ((z : ℂ)^n + ((z⁻¹ : Circle) : ℂ)^n)/2 =
      (if (n : ℤ) = 0 then 1 else 1/2) * pairWeight n z
    cases n with
    | zero => simp [pairWeight]
    | succ n =>
      rw [ite_eq_right (by omega)]
      simp only [pairWeight, Circle.coe_inv]
      ring
  | negSucc n =>
    simp [normalization, pairWeight, Circle.coe_inv, zpow_negSucc, inv_pow]
    ring

variable {I : Type*} [Fintype I]
def coefficients (a : I → ℂ) (p q : I → ℤ) : ℕ × ℕ →₀ ℂ :=
  ∑ i, Finsupp.single ((p i).natAbs, (q i).natAbs)
    (a i * normalization (p i) * normalization (q i))

theorem expansion (f : SU2 → SU2 → ℂ) (a : I → ℂ) (p q : I → ℤ)
    (ht : ∀ z w, f (SU2.torusHom z) (SU2.torusHom w) =
      ∑ i, a i * (z : ℂ)^(p i) * (w : ℂ)^(q i))
    (hz : ∀ z w, f (SU2.torusHom z⁻¹) (SU2.torusHom w) =
      f (SU2.torusHom z) (SU2.torusHom w))
    (hw : ∀ z w, f (SU2.torusHom z) (SU2.torusHom w⁻¹) =
      f (SU2.torusHom z) (SU2.torusHom w)) (z w : Circle) :
    f (SU2.torusHom z) (SU2.torusHom w) = (coefficients a p q).sum
      (fun k b => b * pairWeight k.1 z * pairWeight k.2 w) := by
  classical
  have he : f (SU2.torusHom z) (SU2.torusHom w) =
      (f (SU2.torusHom z) (SU2.torusHom w) +
       f (SU2.torusHom z⁻¹) (SU2.torusHom w) +
       f (SU2.torusHom z) (SU2.torusHom w⁻¹) +
       f (SU2.torusHom z⁻¹) (SU2.torusHom w⁻¹))/4 := by rw [hz,hz,hw]; ring
  rw [he]
  simp only [ht]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.sum_div]
  unfold coefficients
  rw [← Finsupp.sum_finsetSum_index]
  · simp only [Finsupp.sum_single_index, zero_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hp := signed_pair (p i) z
    have hq := signed_pair (q i) w
    calc
      _ = a i * (((z : ℂ)^(p i) + ((z⁻¹ : Circle) : ℂ)^(p i))/2) *
          (((w : ℂ)^(q i) + ((w⁻¹ : Circle) : ℂ)^(q i))/2) := by ring
      _ = _ := by rw [hp,hq]; ring
  · intros; simp
  · intros; ring


theorem coefficient_finrank {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (rho : Representation ℂ (SU2 × SU2) V)
    (hr : ContinuousRepresentationScope.IsJointlyContinuous rho)
    (a : I → ℂ) (p q : I → ℤ)
    (ht : ∀ z w, rho.character (SU2.torusHom z, SU2.torusHom w) =
      ∑ i, a i * (z : ℂ)^(p i) * (w : ℂ)^(q i))
    (hz : ∀ z w, rho.character (SU2.torusHom z⁻¹, SU2.torusHom w) =
      rho.character (SU2.torusHom z, SU2.torusHom w))
    (hw : ∀ z w, rho.character (SU2.torusHom z, SU2.torusHom w⁻¹) =
      rho.character (SU2.torusHom z, SU2.torusHom w)) :
    (Module.finrank ℂ (Representation.IntertwiningMap rho
      (Representation.trivial ℂ (SU2 × SU2) ℂ)) : ℂ) =
      coefficients a p q (0,0) - coefficients a p q (0,2) -
        coefficients a p q (2,0) + coefficients a p q (2,2) :=
  SU2CoefficientExtraction.pair_finrank rho hr _
    (expansion (fun g h => rho.character (g,h)) a p q ht hz hw)

end
end Math.SU2SignedWeights
