import Math.LieGroups.E6.Minuscule.CompactIdentityComponent
import Math.LieGroups.E6.Minuscule.NormalizerCenter
import TauCeti.Analysis.Normed.Algebra.Logarithm.Inverse
import Lean.Util.CollectAxioms

/-!
# E6-0h: identity component, exact exponential directions, scalar center control

The connected candidate is not assumed simply connected. The scalar of
order 27 belongs to the full normalizer; component membership is not asserted.
-/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule NormedSpace
open scoped Matrix Matrix.Norms.L2Operator Topology

example : CompactSpace compactIdentityComponent := inferInstance
example : ConnectedSpace compactIdentityComponent := inferInstance
example : IsTopologicalGroup compactIdentityComponent := inferInstance

example : IsClosed (compactIdentityComponent : Set compactNormalizer) :=
  compactIdentityComponent_isClosed

example : IsConnected (compactIdentityComponent : Set compactNormalizer) :=
  MatrixLieGroupNormalizer.isConnected_identityComponent _

example (X : Matrix27) : X ∈ compactMatrixLieAlgebra ↔
    ∀ t : ℝ, exp (t • X) ∈ compactIdentityMatrices :=
  mem_compactMatrix_iff_exp_mem_identityComponent X

example (k : Fin 3) (i : Fin 6) (t : ℝ) :
    exp (t • (compactGeneratorElement k i).val.val) ∈ compactIdentityMatrices :=
  exp_generator_mem_identityComponent k i t

example : centralScalar27 ∈ Subgroup.center compactNormalizer := centralScalar27_mem_center
example : orderOf centralScalar27 = 27 := centralScalar27_orderOf
example : centralScalar27 ^ (27 : ℕ) = 1 := (centralScalar27_pow_eq_one_iff 27).mpr (dvd_refl _)

theorem centralScalar27_cube_ne_one : centralScalar27 ^ (3 : ℕ) ≠ 1 := by
  intro h
  have hd := (centralScalar27_pow_eq_one_iff 3).mp h
  norm_num at hd

example : centralScalar27 ≠ 1 := by
  intro h
  exact centralScalar27_cube_ne_one (by rw [h, one_pow])

-- These ambient inverse identities do not assert that the logarithm stays in the real form.
theorem matrix_log_exp_near_zero :
    ∀ᶠ X : Matrix27 in 𝓝 0, NormedSpace.log (exp X) = X :=
  by
    let : NormedAlgebra ℚ Matrix27 := NormedAlgebra.restrictScalars ℚ ℂ _
    exact eventually_log_exp Matrix27

theorem matrix_exp_log_near_one :
    ∀ᶠ X : Matrix27 in 𝓝 1, exp (NormedSpace.log X) = X :=
  by
    let : NormedAlgebra ℚ Matrix27 := NormedAlgebra.restrictScalars ℚ ℂ _
    exact eventually_exp_log Matrix27

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.MatrixLieGroupNormalizer.isClosed_identityComponent,
    ``Math.MatrixLieGroupNormalizer.isConnected_identityComponent,
    ``Math.MatrixLieGroupNormalizer.componentMatrices_le,
    ``Math.MatrixLieGroupNormalizer.exponentialLine,
    ``Math.MatrixLieGroupNormalizer.exponentialLine_zero,
    ``Math.MatrixLieGroupNormalizer.continuous_exponentialLine,
    ``Math.MatrixLieGroupNormalizer.exponentialLine_mem_identityComponent,
    ``Math.MatrixLieGroupNormalizer.exp_mem_componentMatrices_iff,
    ``Math.MatrixLieGroupNormalizer.scalarSpecial,
    ``Math.MatrixLieGroupNormalizer.conjugate_scalarSpecial,
    ``Math.MatrixLieGroupNormalizer.scalarSpecial_mem,
    ``Math.MatrixLieGroupNormalizer.scalarElement,
    ``Math.MatrixLieGroupNormalizer.scalarElement_mem_center,
    ``Math.MatrixLieGroupNormalizer.scalarElement_pow_coe,
    ``Math.E6.Minuscule.compactIdentityComponent_isClosed,
    ``Math.E6.Minuscule.compactIdentityComponent_isCompact,
    ``Math.E6.Minuscule.mem_compactMatrix_iff_exp_mem_identityComponent,
    ``Math.E6.Minuscule.exp_compactRealForm_mem_identityComponent,
    ``Math.E6.Minuscule.exp_generator_mem_identityComponent,
    ``Math.E6.Minuscule.scalarRoot27_primitive,
    ``Math.E6.Minuscule.scalarUnitary27,
    ``Math.E6.Minuscule.centralScalar27,
    ``Math.E6.Minuscule.centralScalar27_mem_center,
    ``Math.E6.Minuscule.centralScalar27_pow_coe,
    ``Math.E6.Minuscule.centralScalar27_pow_eq_one_iff,
    ``Math.E6.Minuscule.centralScalar27_orderOf,
    ``Math.E6.Minuscule.compactNormalizer_center_not_exponent_three,
    ``Math.E6.Minuscule.compactNormalizer_not_equiv_of_center_exponent_three,
    ``Math.E6.Audit.centralScalar27_cube_ne_one,
    ``Math.E6.Audit.matrix_log_exp_near_zero,
    ``Math.E6.Audit.matrix_exp_log_near_one]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0h: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0h: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0h: checked {declarations.length} declarations against the standard axiom allowlist"
