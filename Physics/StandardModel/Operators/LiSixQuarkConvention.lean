import Physics.StandardModel.Operators.LiSixQuarkExtension
import Physics.StandardModel.Operators.LiSixQuarkFiniteData
import Physics.StandardModel.Operators.LiSixQuarkSourceTransport
import Physics.StandardModel.Operators.LiSixQuarkReducedSeeds

/-! Literal epsilon/Young data for Li 2007.07899v1 (5.63), followed by one
explicit extension. Indices 0--9 are printed; index 10 is not in the paper.
Row then column action and the fermionic transfer sign are fixed here. -/
namespace GUT.LiSixQuarkConvention
set_option autoImplicit false
noncomputable section
open SixQuarkInvariant SMEpsilonTensor

abbrev permutation := LiSixQuarkLiteralSource.permutation
abbrev seedColorPerm := LiSixQuarkLiteralSource.seedColorPerm
abbrev spinPerm := LiSixQuarkLiteralSource.spinPerm
abbrev paperToRepo := LiSixQuarkLiteralSource.paperToRepo
abbrev seed := LiSixQuarkLiteralSource.seed
abbrev candidate := LiSixQuarkLiteralSource.candidate

theorem candidate_invariant (k : Fin 11) : IsInvariant (candidate k) :=
  LiSixQuarkLiteralSource.candidate_invariant k

theorem colorEpsilon_cast (a b c : Fin 3) :
    eps3 (colorBasis a) (colorBasis b) (colorBasis c) = (colorEpsilon a b c : ℂ) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [eps3, colorBasis, colorEpsilon, basisEntry, Pi.single_apply, Fin.ext_iff]

theorem spinEpsilon_cast (a b : Fin 2) :
    eps2 (weakBasis a) (weakBasis b) = (spinEpsilon a b : ℂ) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [eps2, weakBasis, spinEpsilon, basisEntry, Pi.single_apply, Fin.ext_iff]

theorem candidate_basis (k : Fin 11) (v : Fin 6 → Fin 3) (s : Fin 6 → Fin 2) :
    candidate k (fun i => colorBasis (v i) ⊗ₜ[ℂ] weakBasis (s i)) =
      (rationalValue k v s : ℂ) := by
  change LiSixQuarkLiteralSource.candidate k
    (fun i => colorBasis (v i) ⊗ₜ[ℂ] weakBasis (s i)) = _
  simp only [LiSixQuarkLiteralSource.candidate, MultilinearMap.domDomCongr_apply,
    sum_apply, smul_apply, LiSixQuarkLiteralSource.seed, combine_apply, SixColorInvariant.pairing_apply,
    SixWeylMultilinear.pairing_apply, SixColorInvariant.pairingValue,
    SixWeylMultilinear.pairingValue, SixWeylInvariant.pairingValue,
    colorEpsilon_cast, spinEpsilon_cast]
  simp [rationalValue, LiSixQuarkLiteralSource.permutation,
    LiSixQuarkLiteralSource.seedColorPerm, LiSixQuarkLiteralSource.paperToRepo,
    LiSixQuarkLiteralSource.spinPerm,
    smul_eq_mul, Rat.cast_sum, Rat.cast_mul, Rat.cast_div]

theorem seedCoordinates_semantic (k : Fin 11) :
    seedCoordinates k = LiSixQuarkSemanticSeeds.seedCoordinates k :=
  LiSixQuarkSeedRecipe.rational_cast k

theorem candidate_coordinates (k : Fin 11) :
    coordinates (candidate k) = seedCoordinates k := by
  change coordinates (LiSixQuarkLiteralSource.candidate k) = seedCoordinates k
  rw [LiSixQuarkSourceTransport.candidate_coordinates, seedCoordinates_semantic]

theorem extra_agrees : candidate 10 = LiSixQuarkExtension.coefficient := by
  apply eq_of_coordinates (candidate_invariant _) LiSixQuarkExtension.coefficient_invariant
  rw [candidate_coordinates, seedCoordinates_semantic,
    LiSixQuarkReducedSeeds.extra_seed, LiSixQuarkExtension.coefficient_coordinates]

end
end GUT.LiSixQuarkConvention
