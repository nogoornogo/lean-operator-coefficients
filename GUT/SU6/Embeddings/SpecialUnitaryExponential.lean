import GUT.SU6.Embeddings.HighestWeightBridge
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic

open Math

/-!
# Concrete exponentials in the compact special-unitary groups

This file records group-specific matrix-exponential calculations used by the
analytic semisimple embedding classification source bridge.  It begins with the compact Cartan element of
`SU(2)` whose exponential is the nontrivial center element.
-/

namespace GUT
namespace SpecialUnitaryExponential

open CompactEmbeddingClassification HighestWeightBridge

noncomputable section

open NormedSpace

/-- The matrix underlying `pi * I * H` is diagonal with entries `pi * I` and
`-pi * I`. -/
theorem su2CenterLieElement_coe :
    ((su2CenterLieElement : StandardSl2.Algebra) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![((Real.pi : ℂ) * Complex.I),
        -((Real.pi : ℂ) * Complex.I)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2CenterLieElement, StandardSl2.H]

/-- The compact-real-form element `pi * I * H` exponentiates to `-I_2`. -/
theorem exp_su2CenterLieElement :
    exp
        ((su2CenterLieElement : StandardSl2.Algebra) :
          Matrix (Fin 2) (Fin 2) ℂ) =
      ((su2CenterElement : SU2) : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [su2CenterLieElement_coe, Matrix.exp_diagonal,
    CompactEmbeddingClassification.su2CenterElement_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [← Complex.exp_eq_exp_ℂ, Complex.exp_pi_mul_I,
      Complex.exp_neg_pi_mul_I]

end

end SpecialUnitaryExponential
end GUT
