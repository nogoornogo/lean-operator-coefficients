import Physics.StandardModel.Operators.DevMohapatraHeavyAction

/-! Holomorphic projection of the exact all-order stationary solution.
No zero barred-heavy hypothesis or degree truncation. -/
namespace GUT.DevMohapatraHeavyProjection
set_option autoImplicit false
noncomputable section
open DevMohapatraHeavyElimination DevMohapatraTreeLevel
open scoped Matrix
abbrev Light := Fin 18 → ℂ

def holomorphicFields : V →ₗ[ℂ] Light where
  toFun v i := v ⟨i.val, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def project : R →ₐ[ℂ] ExteriorAlgebra ℂ Light := ExteriorAlgebra.map holomorphicFields

def ul (c : Fin 3) (r : Fin 2) := holomorphicFields (u c r)
def dl (c : Fin 3) (r : Fin 2) := holomorphicFields (d c r)
def sl (c : Fin 3) (r : Fin 2) := holomorphicFields (s c r)

theorem holomorphicFields_bar (c : Fin 3) (r : Fin 2) :
    holomorphicFields (ub c r) = 0 ∧ holomorphicFields (db c r) = 0 ∧ holomorphicFields (sb c r) = 0 := by
  constructor
  · ext i; simp [holomorphicFields, ub, coord, Pi.basisFun_apply, Pi.single_apply]; omega
  · constructor
    · ext i; simp [holomorphicFields, db, coord, Pi.basisFun_apply, Pi.single_apply]; omega
    · ext i; simp [holomorphicFields, sb, coord, Pi.basisFun_apply, Pi.single_apply]; omega

theorem project_current (r : Fin 2) : project (current u d s r) = current ul dl sl r := by
  simp [project, current, term, cubic_apply, ul, dl, sl, map_sum, map_mul,
    ExteriorAlgebra.map_apply_ι]

theorem project_bar_current (r : Fin 2) : project (current ub db sb r) = 0 := by
  simp [project, current, term, cubic_apply, map_sum, map_mul, ExteriorAlgebra.map_apply_ι,
    (holomorphicFields_bar _ _).1, (holomorphicFields_bar _ _).2.1, (holomorphicFields_bar _ _).2.2]

theorem project_cross (r t : Fin 2) : project (cross r t) = 0 := by
  simp [project, cross, map_sum, map_mul, ExteriorAlgebra.map_apply_ι, (holomorphicFields_bar _ _).1]

theorem project_kernel (m M a : ℂ) (i j : Fin 4) : project (kernel m M a i j) = 0 := by
  fin_cases i <;> fin_cases j <;> simp [kernel, project_cross]

theorem project_solution_source (m M a b : ℂ) (i : Fin 4) :
    project (solution m M a b i) = project (source m M a b i) := by
  have h := congrArg project (congrFun (source_equation m M a b) i)
  simpa [Pi.sub_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, project_kernel] using h

theorem project_bar_solution (m M a b : ℂ) :
    project (solution m M a b 2) = 0 ∧ project (solution m M a b 3) = 0 := by
  simp [project_solution_source, source, project_bar_current]

theorem project_constant (m b : ℂ) : project (constant m b) = 0 := by
  simp [constant, map_sum, map_mul, downCurrent, pair, project,
    ExteriorAlgebra.map_apply_ι, (holomorphicFields_bar _ _).2.1, (holomorphicFields_bar _ _).2.2]

/-- Exact all-order elimination gives the earlier holomorphic polynomial;
barred-heavy vanishing is proved from the coupled stationary solution. -/
theorem project_eliminated_action (m M a b : ℂ) (hM : M ≠ 0) :
    project (action m M a b (solution m M a b)) = generated m M a b ul dl sl := by
  rw [DevMohapatraHeavyElimination.eliminated_action m M a b hM]
  simp [linear, map_mul, project_solution_source, source, project_current,
    project_bar_current, project_constant, generated, effectiveCoupling,
    current_swap ul dl sl 1 0, smul_smul]
  module

end
end GUT.DevMohapatraHeavyProjection
