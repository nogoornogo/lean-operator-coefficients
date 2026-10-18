import Physics.StandardModel.Operators.DevMohapatraHeavyHermitian
import Physics.StandardModel.Operators.DevMohapatraLiteratureConvention

/-! All-degree Hermitian elimination composed with the literature dictionary.
Source adoption and canonical normalization remain explicit application inputs. -/
namespace GUT.DevMohapatraCoefficientReevaluation
set_option autoImplicit false
noncomputable section
open DevMohapatraHeavyElimination DevMohapatraHeavyAction
open DevMohapatraHeavyProjection DevMohapatraLiteratureConvention

/-- Both inverse-C vertices are transported, before full heavy elimination. -/
def projectedAction (m M lam b : ℂ) : ExteriorAlgebra ℂ Light :=
  project (evaluate (solution m M (-lam) (-b)) (solution_odd m M (-lam) (-b))
    (DevMohapatraHeavyHermitian.literalEffective m M (-lam) (-b)))

theorem projectedAction_coefficient (m M lam b : ℂ) (hM : M ≠ 0) :
    projectedAction m M lam b = coefficient m M lam b • operator ul dl sl := by
  rw [projectedAction, DevMohapatraHeavyHermitian.action_dictionary,
    DevMohapatraHeavyAction.evaluated_action,
    project_eliminated_action m M (-lam) (-b) hM,
    generated_literature]

theorem independent_comparison (m M lam z : ℂ) (hm : m ≠ 0) (hM : M ≠ 0) :
    projectedAction m M lam z =
      (-(8 * (Real.pi : ℂ)^2) * DevMohapatraTreeLevel.paperPrefactor m M lam z) •
        operator ul dl sl := by
  rw [projectedAction_coefficient m M lam z hM, paper_comparison m M lam z hm hM]

theorem ordered_comparison (m M lam z : ℂ) (hm : m ≠ 0) (hM : M ≠ 0) :
    projectedAction m M lam (2*z) =
      (-(32 * (Real.pi : ℂ)^2) * DevMohapatraTreeLevel.paperPrefactor m M lam z) •
        operator ul dl sl := by
  rw [projectedAction_coefficient m M lam (2*z) hM,
    ordered_paper_comparison m M lam z hm hM]

end
end GUT.DevMohapatraCoefficientReevaluation
