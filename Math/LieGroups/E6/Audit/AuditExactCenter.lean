import Math.LieGroups.E6.Minuscule.ExactCenter
import Lean.Util.CollectAxioms

/-! The nonzero cubic is invariant under the actual connected candidate,
whose center is exactly the cube roots of unity. No global classification
or simple connectedness certificate is an input to these statements. -/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule
open scoped Matrix Matrix.Norms.L2Operator

example : cubic cubicWitness = 1 := cubic_witness
example (z : ℂ) (v : Fin 27 → ℂ) : cubic (z • v) = z ^ 3 * cubic v := cubic_homogeneous z v

-- Removing almost all terms does not pass the infinitesimal checker.
example : SparseCubicCertificate.checkZero
    (SparseCubicCertificate.act (LieData.e6Basis 0) [((0, 12, 26), 1)]) = false := by
  decide +kernel

example (X : Matrix27) (hX : X ∈ matrixLieAlgebra ℂ) (v : Fin 27 → ℂ) :
    SparseCubicCertificate.differential cubicCode v (X *ᵥ v) = 0 :=
  cubic_infinitesimal X hX v

example (g : compactIdentityComponent) (v : Fin 27 → ℂ) :
    cubic (compactMatrix g *ᵥ v) = cubic v := cubic_invariant g v

example : Nat.card (Subgroup.center compactIdentityComponent) = 3 := compactCenter_card

example : Subgroup.center compactIdentityComponent ≃* rootsOfUnity 3 ℂ :=
  compactCenterEquivCubeRoots

example : centralScalar27 ∉ compactIdentityComponent := centralScalar27_not_mem
example : centralScalar27 ^ 9 ∈ compactIdentityComponent := centralScalar27_pow_nine_mem

-- The connected candidate and full normalizer must still be distinguished.
example : ¬∀ g ∈ Subgroup.center compactNormalizer, g ^ (3 : ℕ) = 1 :=
  compactNormalizer_center_not_exponent_three

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.SparseCubicCertificate.eval_smul,
    ``Math.SparseCubicCertificate.checkZero_sound,
    ``Math.SparseCubicCertificate.eval_act,
    ``Math.SparseCubicCertificate.checked_mem_annihilator,
    ``Math.SparseCubicCertificate.hasDerivAt_eval,
    ``Math.SparseCubicCertificate.hasDerivAt_exp_mulVec,
    ``Math.SparseCubicCertificate.eval_exp_of_infinitesimal,
    ``Math.E6.Minuscule.cubic_checked,
    ``Math.E6.Minuscule.cubic_witness,
    ``Math.E6.Minuscule.cubic_ne_zero,
    ``Math.E6.Minuscule.cubic_homogeneous,
    ``Math.E6.Minuscule.cubic_infinitesimal,
    ``Math.E6.Minuscule.cubic_real_infinitesimal,
    ``Math.E6.Minuscule.cubic_exp,
    ``Math.E6.Minuscule.compactIdentityComponent_le_cubicStabilizer,
    ``Math.E6.Minuscule.cubic_invariant,
    ``Math.E6.Minuscule.compact_scalar_cube,
    ``Math.E6.Minuscule.compactCenterScalar_cube,
    ``Math.E6.Minuscule.compactCenterCubeRoot_injective,
    ``Math.E6.Minuscule.compactCenter_card,
    ``Math.E6.Minuscule.compactCenterEquivCubeRoots,
    ``Math.E6.Minuscule.compact_center_cube,
    ``Math.E6.Minuscule.centralScalar27_not_mem]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6 exact center: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6 exact center: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6 exact center: checked {declarations.length} declarations"
