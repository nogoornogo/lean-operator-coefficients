import Math.LieGroups.E6.Minuscule.CubicInvariant
import Math.LieGroups.E6.Minuscule.CompactLieGroup
import Math.LieAlgebras.CubicExponential

/-! The actual connected candidate preserves the nonzero cubic on its 27.
This uses its proved algebraic generation by real-form exponentials. -/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

theorem cubic_exp (X : compactMatrixLieAlgebra) (v : Fin 27 → ℂ) :
    cubic (exp (X : Matrix27) *ᵥ v) = cubic v :=
  SparseCubicCertificate.eval_exp_of_infinitesimal cubicCode X (cubic_real_infinitesimal X) v

def cubicStabilizer : Subgroup compactNormalizer where
  carrier := {g | ∀ v : Fin 27 → ℂ, cubic ((g.val : Matrix27) *ᵥ v) = cubic v}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro g h hg hh v
    change cubic (((g.val : Matrix27) * (h.val : Matrix27)) *ᵥ v) = cubic v
    rw [← Matrix.mulVec_mulVec, hg, hh]
  inv_mem' := by
    intro g hg v
    have h := hg (((g⁻¹).val : Matrix27) *ᵥ v)
    rw [Matrix.mulVec_mulVec] at h
    change cubic ((((g * g⁻¹).val : Matrix27)) *ᵥ v) = _ at h
    simpa using h.symm

theorem compactIdentityComponent_le_cubicStabilizer : compactIdentityComponent ≤ cubicStabilizer := by
  rw [← compactExponentialSubgroup_eq_identityComponent]
  apply (Subgroup.closure_le cubicStabilizer).mpr
  rintro g ⟨X, hX, he⟩ v
  rw [← he]
  exact cubic_exp ⟨X, hX⟩ v

theorem cubic_invariant (g : compactIdentityComponent) (v : Fin 27 → ℂ) :
    cubic (compactMatrix g *ᵥ v) = cubic v :=
  compactIdentityComponent_le_cubicStabilizer g.property v

end

end Math.E6.Minuscule
