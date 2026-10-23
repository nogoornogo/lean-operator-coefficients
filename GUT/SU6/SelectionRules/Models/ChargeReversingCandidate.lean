import GUT.SU6.SelectionRules.Models.AutomorphismCovariantModel
import Math.RepresentationTheory.Invariants.CovariantCharacterObstruction
import Physics.StandardModel.Spectrum.Representations.HyperchargeReversalProbe

open Physics

/-! A charge-reversing linear residual candidate can fail already at the light
SM-index condition. This is not a general noncommuting-symmetry no-go. -/
namespace GUT.ChargeReversingCandidate
set_option autoImplicit false
noncomputable section
open Math Representation AutomorphismCovariantModel
variable {H K : Type*} [CommGroup H] [TopologicalSpace H]
  [Group K] [TopologicalSpace K] (M : Model H K)

theorem light_dual_index_zero (h : H) (g : K) (hg : M.beta h g = g⁻¹) :
    M.mass.radical.toRepresentation.character g -
      M.mass.radical.toRepresentation.dual.character g = 0 :=
  CovariantCharacterObstruction.dual_index_zero_of_inverse
    M.mass.radical.toRepresentation M.beta (lightAction M) h g hg

/-- An independently verified chiral target probe excludes the reversing
candidate before any Lorentz or coefficient-Hom calculation is needed. -/
theorem no_positive_target {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (target : Representation ℂ K W) (n : ℕ)
    (h : H) (g : K) (hg : M.beta h g = g⁻¹)
    (ht : target.character g - target.dual.character g ≠ 0) :
    ¬ HasPositiveDualTarget M target n := by
  rintro ⟨hn, htarget⟩
  have he := (htarget g).symm.trans (light_dual_index_zero M h g hg)
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  exact ht ((mul_eq_zero.mp he).resolve_left hn')

/-- Actual SM character dictionary along a gauge-cover homomorphism. No
injective embedding of the SM covering product into SU(6) is required. -/
theorem no_sm_positive_target {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (target : Representation ℂ K W)
    (cover : StandardSMGaugeTensor.GaugeGroup →* K)
    (dictionary : ∀ g, target.character (cover g) = ExactSMSpectrum.generation.character g)
    (n : ℕ) (h : H)
    (hg : M.beta h (cover HyperchargeReversalProbe.probe) =
      (cover HyperchargeReversalProbe.probe)⁻¹) :
    ¬ HasPositiveDualTarget M target n := by
  have ht : target.character (cover HyperchargeReversalProbe.probe) -
      target.dual.character (cover HyperchargeReversalProbe.probe) ≠ 0 := by
    rw [target.char_dual, ← map_inv, dictionary, dictionary]
    simpa only [ExactSMSpectrum.generation.char_dual] using
      HyperchargeReversalProbe.generation_probe_nonzero
  exact no_positive_target M target n h (cover HyperchargeReversalProbe.probe) hg ht

/-- Probe reversal up to conjugation in the actual unbroken gauge group. -/
theorem no_positive_target_of_conjugate_inverse {W : Type*}
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (target : Representation ℂ K W) (n : ℕ) (h : H) (g c : K)
    (hg : M.beta h g = c * g⁻¹ * c⁻¹)
    (ht : target.character g - target.dual.character g ≠ 0) :
    ¬ HasPositiveDualTarget M target n := by
  rintro ⟨hn, htarget⟩
  have hz := CovariantCharacterObstruction.dual_index_zero_of_conjugate_inverse
    M.mass.radical.toRepresentation M.beta (lightAction M) h g c hg
  have he := (htarget g).symm.trans hz
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  exact ht ((mul_eq_zero.mp he).resolve_left hn')

/-- The actual SM probe exclusion is unchanged by a supplied unbroken-gauge
conjugation. This does not classify all outer automorphisms. -/
theorem no_sm_positive_target_of_conjugate_inverse {W : Type*}
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (target : Representation ℂ K W)
    (cover : StandardSMGaugeTensor.GaugeGroup →* K)
    (dictionary : ∀ g, target.character (cover g) = ExactSMSpectrum.generation.character g)
    (n : ℕ) (h : H) (c : K)
    (hg : M.beta h (cover HyperchargeReversalProbe.probe) =
      c * (cover HyperchargeReversalProbe.probe)⁻¹ * c⁻¹) :
    ¬ HasPositiveDualTarget M target n := by
  have ht : target.character (cover HyperchargeReversalProbe.probe) -
      target.dual.character (cover HyperchargeReversalProbe.probe) ≠ 0 := by
    rw [target.char_dual, ← map_inv, dictionary, dictionary]
    simpa only [ExactSMSpectrum.generation.char_dual] using
      HyperchargeReversalProbe.generation_probe_nonzero
  exact no_positive_target_of_conjugate_inverse M target n h
    (cover HyperchargeReversalProbe.probe) c hg ht

end
end GUT.ChargeReversingCandidate
