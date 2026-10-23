import Physics.StandardModel.Spectrum.Representations.ExactSMResidualSpectrum
import Physics.StandardModel.Spectrum.Representations.GaugeTorusTrace

open Math

/-! The exact SM-only spectrum determines actual torus multiplicities. This
step forgets H; residual-equivariant comparisons are constructed separately. -/

namespace Physics.ExactSMWeightMultiplicity
noncomputable section
open scoped BigOperators
open Representation StandardSMGaugeTensor ExactSMSpectrum FiniteSpectrum
open SU5 SU5.TorusCharacter SU5.TorusMatterCharacter StandardSMCharacterTarget
open ResidualWeightSpace ResidualWeightCharacter ProductFactorization InvariantWeylMass

theorem generation_trace (z : PhysicalTorus.Coordinates) :
    generation.character (PhysicalTorus.gaugePoint z) =
      ∑ i : Fin 15, (weightCharacter (smReducedWeight i) (PhysicalTorus.toTorus z) : ℂ) := by
  simp only [generation, character_prod, char_dual, quark, upRight, downRight,
    lepton, electronRight, character_twist, char_tensor, Pi.mul_apply]
  rw [color_character, color_character_inv, weak_character]
  have ht (g : GaugeGroup) : (Representation.trivial ℂ GaugeGroup ℂ).character g = 1 := by
    change LinearMap.trace ℂ ℂ LinearMap.id = 1
    simp
  rw [ht]
  simp_rw [PhysicalTorus.weightCharacter_toTorus]
  norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, smReducedWeight,
    PhysicalTorus.exponent, phase, PhysicalTorus.gaugePoint]
  field_simp
  ring

def polynomial (n s : ℕ) : Polynomial (T := MaximalTorus.Torus) :=
  (∑ i : Fin 15, Finsupp.single (weightCharacter (smReducedWeight i)) (n : ℂ)) +
    Finsupp.single 1 (s : ℂ)

theorem eval_polynomial (n s : ℕ) (t : MaximalTorus.Torus) :
    ResidualWeightCharacter.eval (polynomial n s) t =
      (n : ℂ) * (∑ i : Fin 15, (weightCharacter (smReducedWeight i) t : ℂ)) + s := by
  classical
  unfold polynomial ResidualWeightCharacter.eval
  rw [Finsupp.sum_add_index]
  · rw [← Finsupp.sum_finsetSum_index]
    · simp [Finset.mul_sum]
    · intros; simp
    · intros; simp [add_mul]
  · intros; simp
  · intros; simp [add_mul]

theorem action_trace (n s : ℕ) (z : PhysicalTorus.Coordinates) :
    (action n s).character (PhysicalTorus.gaugePoint z) =
      ResidualWeightCharacter.eval (polynomial n s) (PhysicalTorus.toTorus z) := by
  rw [action, character_prod, character_copies, generation_trace, eval_polynomial]
  congr 1
  change LinearMap.trace ℂ (Fin s → ℂ) LinearMap.id = (s : ℂ)
  simp

@[simp] theorem weight_zero : weightCharacter 0 = 1 := by
  apply MonoidHom.ext
  intro t
  obtain ⟨z, rfl⟩ := PhysicalTorus.toTorus_surjective t
  simp [PhysicalTorus.weightCharacter_toTorus, PhysicalTorus.exponent, Fin.prod_univ_succ]

@[simp] theorem weight_neg (w : StandardAbelianCharge.ReducedWeight) :
    weightCharacter (-w) = (weightCharacter w)⁻¹ := by
  apply MonoidHom.ext
  intro t
  obtain ⟨z, rfl⟩ := PhysicalTorus.toTorus_surjective t
  have he : PhysicalTorus.exponent (-w) = -PhysicalTorus.exponent w := by
    ext i
    fin_cases i <;> simp [PhysicalTorus.exponent] <;> ring
  simp only [MonoidHom.inv_apply, PhysicalTorus.weightCharacter_toTorus,
    he, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]

theorem polynomial_positive (n s : ℕ) (i : Fin 15) :
    polynomial n s (weightCharacter (smReducedWeight i)) = n := by
  classical
  have hz : weightCharacter (smReducedWeight i) ≠ 1 := by
    rw [← weight_zero]
    exact fun h => smReducedWeight_nonzero i (weightCharacter_injective h)
  have he (j : Fin 15) : weightCharacter (smReducedWeight j) =
      weightCharacter (smReducedWeight i) ↔ j = i :=
    weightCharacter_injective.eq_iff.trans (smReducedWeight_inj j i)
  simp [polynomial, Finsupp.single_apply, he, hz]

theorem polynomial_negative (n s : ℕ) (i : Fin 15) :
    polynomial n s (weightCharacter (smReducedWeight i))⁻¹ = 0 := by
  classical
  rw [← weight_neg]
  have hz : weightCharacter (-smReducedWeight i) ≠ 1 := by
    rw [← weight_zero]
    exact fun h => neg_ne_zero.mpr (smReducedWeight_nonzero i) (weightCharacter_injective h)
  have he (j : Fin 15) : weightCharacter (smReducedWeight j) ≠
      weightCharacter (-smReducedWeight i) :=
    fun h => StandardWeylDualTarget.smReducedWeight_ne_neg j i (weightCharacter_injective h)
  simp only [polynomial, Finsupp.add_apply, Finsupp.finsetSum_apply,
    Finsupp.single_apply, he, ite_false, Finset.sum_const_zero,
    Ne.symm hz, zero_add]

variable {H G E : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : MaximalTorus.Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation
    (torus (rho.comp (j.prodMap (MonoidHom.id H)))))

theorem coefficients_eq {n s : ℕ}
    (hs : HasSpectrum (firstRestriction D.action) n s) :
    coefficients B.radical.toRepresentation
      (ResidualMassIndex.light_torus_unitary j rho B hu) 1 = polynomial n s := by
  apply ResidualWeightCharacter.eval_injective
  intro t
  obtain ⟨z, rfl⟩ := PhysicalTorus.toTorus_surjective t
  rw [eval_coefficients]
  have ha := DFunLike.congr_fun D.restriction (z, (1 : H))
  change D.action (PhysicalTorus.gaugePoint z, 1) =
    B.radical.toRepresentation (PhysicalTorus.toTorus z, 1) at ha
  change LinearMap.trace ℂ _ _ = _
  rw [← ha]
  change (firstRestriction D.action).character (PhysicalTorus.gaugePoint z) = _
  obtain ⟨e⟩ := hs
  rw [char_iso e]
  exact action_trace n s z

include hu in
theorem weight_finrank {n s : ℕ}
    (hs : HasSpectrum (firstRestriction D.action) n s) (i : Fin 15) :
    Module.finrank ℂ (space B.radical.toRepresentation (weightCharacter (smReducedWeight i))) = n := by
  have h := congrArg (fun p => p (weightCharacter (smReducedWeight i)))
    (coefficients_eq j rho B D hu hs)
  rw [coefficients_apply, char_one, polynomial_positive] at h
  exact_mod_cast h

include hu in
theorem opposite_weight_finrank {n s : ℕ}
    (hs : HasSpectrum (firstRestriction D.action) n s) (i : Fin 15) :
    Module.finrank ℂ (space B.radical.toRepresentation (weightCharacter (smReducedWeight i))⁻¹) = 0 := by
  have h := congrArg (fun p => p (weightCharacter (smReducedWeight i))⁻¹)
    (coefficients_eq j rho B D hu hs)
  rw [coefficients_apply, char_one, polynomial_negative] at h
  exact_mod_cast h

end
end Physics.ExactSMWeightMultiplicity
