import GUT.SU6.SelectionRules.Models.AutomorphismCovariantModel
import Math.RepresentationTheory.DualIndexCompatibility
import Physics.StandardModel.Spectrum.ExactSMSpectrum

/-! Necessary target compatibility for arbitrary supplied normalizing actions.
No full light-spectrum dictionary is inferred from this criterion. -/
namespace GUT.TargetIndexCompatibility
set_option autoImplicit false
noncomputable section
open Math Representation AutomorphismCovariantModel
variable {H K : Type*} [CommGroup H] [TopologicalSpace H]
  [Group K] [TopologicalSpace K] (M : Model H K)
  {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (target : Representation ℂ K W) (n : ℕ)

/-- The whole target dual-index function must be preserved, not just one probe. -/
theorem target_index_invariant (ht : HasPositiveDualTarget M target n)
    (h : H) (g : K) :
    target.character (M.beta h g) - target.dual.character (M.beta h g) =
      target.character g - target.dual.character g := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt ht.1)
  apply mul_left_cancel₀ hn
  exact (ht.2 (M.beta h g)).symm.trans
    ((DualIndexCompatibility.dual_index_invariant
      M.mass.radical.toRepresentation M.beta (lightAction M) h g).trans (ht.2 g))

/-- Rejection test also applicable to non-reversing automorphisms. -/
theorem no_positive_target_of_mismatch (h : H) (g : K)
    (hm : target.character (M.beta h g) - target.dual.character (M.beta h g) ≠
      target.character g - target.dual.character g) :
    ¬ HasPositiveDualTarget M target n := by
  intro ht
  exact hm (target_index_invariant M target n ht h g)
/-- Check any supplied image of an SM-cover element, not only its inverse. -/
theorem no_sm_positive_target_of_mismatch
    (cover : StandardSMGaugeTensor.GaugeGroup →* K)
    (dictionary : ∀ g, target.character (cover g) = ExactSMSpectrum.generation.character g)
    (h : H) (g g' : StandardSMGaugeTensor.GaugeGroup)
    (hg : M.beta h (cover g) = cover g')
    (hm : ExactSMSpectrum.generation.character g' -
      ExactSMSpectrum.generation.dual.character g' ≠
      ExactSMSpectrum.generation.character g - ExactSMSpectrum.generation.dual.character g) :
    ¬ HasPositiveDualTarget M target n := by
  apply no_positive_target_of_mismatch M target n h (cover g)
  rw [hg]
  simp only [target.char_dual, ← map_inv, dictionary]
  simpa only [ExactSMSpectrum.generation.char_dual] using hm

end
end GUT.TargetIndexCompatibility
