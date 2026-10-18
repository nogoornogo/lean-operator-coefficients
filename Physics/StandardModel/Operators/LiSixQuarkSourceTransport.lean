import Physics.StandardModel.Operators.LiSixQuarkLiteralSource
import Physics.StandardModel.Operators.LiSixQuarkSemanticSeeds
import Physics.StandardModel.Operators.LiSixQuarkYoungExpansion

/-! The literal paper convention and the factored action on actual epsilon
sources describe the same multilinear coefficients. -/
namespace GUT.LiSixQuarkSourceTransport
noncomputable section
open SixQuarkInvariant LiSixQuarkLiteralSource LiSixQuarkSemanticSeeds
open LiSixQuarkYoungOperators LiSixQuarkYoungExpansion

theorem raw_source (k : Fin 11) :
    LiSixQuarkRawSource.rawCoefficient k = (seed k).domDomCongr paperToRepo := by
  apply pure_ext
  intro v s
  fin_cases k <;>
    simp [LiSixQuarkRawSource.rawCoefficient, LiSixQuarkRawSource.rawColor,
      LiSixQuarkRawSource.rawSpin, LiSixQuarkRawSource.colorKind,
      LiSixQuarkRawSource.colorPermutation, LiSixQuarkRawSource.spinPermutation,
      seed, seedColorPerm, paperToRepo, spinPerm, LiSixQuarkYoungData.seedColorData,
      combine_apply, SixColorInvariant.pairing_apply,
      SixWeylMultilinear.pairing_apply, SixColorInvariant.pairingValue,
      SixWeylMultilinear.pairingValue, SixWeylInvariant.pairingValue,
      MultilinearMap.domDomCongr_apply]

def evaluateLinear : Coefficient →ₗ[ℂ] ((Fin 6 → Quark) → ℂ) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluate_action (g : Fin 4) (f : Coefficient) :
    evaluateLinear (coefficientAction g f) = functionAction g (evaluateLinear f) := rfl

theorem candidate_eq_semantic (k : Fin 11) : candidate k = seedCoefficient k := by
  ext v
  have h := map_young evaluateLinear coefficientAction functionAction evaluate_action k
    (LiSixQuarkRawSource.rawCoefficient k)
  have he := congrFun h v
  change seedCoefficient k v = _ at he
  rw [he, ← normalized_eq_young]
  simp only [candidate, MultilinearMap.domDomCongr_apply, sum_apply, smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  rw [raw_source]
  simp only [evaluateLinear, LinearMap.coe_mk, AddHom.coe_mk,
    MultilinearMap.domDomCongr_apply]
  congr 1
  ext i
  change v (paperToRepo (permutation g i)) = v (repoMap g (paperToRepo i))
  exact congrArg v (repoMap_paperMap g i).symm

theorem candidate_coordinates (k : Fin 11) :
    coordinates (candidate k) = seedCoordinates k := by
  rw [candidate_eq_semantic, coordinates_seedCoefficient]

end
end GUT.LiSixQuarkSourceTransport
