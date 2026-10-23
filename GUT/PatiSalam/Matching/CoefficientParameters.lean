import Math.LinearAlgebra.Constructions.TwoSourceQuadraticElimination
import GUT.PatiSalam.Matching.NeutralMass

/-! Parameter algebra of the specified scalar-mediated PS path.
The contraction-to-sector correspondence is a separate obligation. -/
namespace GUT.PatiSalam.CoefficientParameters
set_option autoImplicit false
noncomputable section

def diquark (C v Lambda : ℂ) := C * v / Lambda
/-- v is <chi0> = vR/sqrt(2), m is the selected scalar mass squared.
The minus Yukawa sign is part of the specified source convention. -/
def generated (C v Lambda y p m : ℂ) := -(diquark C v Lambda * (-y*p) / m)

theorem generated_formula (C v Lambda y p m : ℂ) :
    generated C v Lambda y p m = C*v*y*p/(Lambda*m) := by
  unfold generated diquark
  ring

theorem generated_nonzero_iff (C v Lambda y p m : ℂ)
    (hLambda : Lambda ≠ 0) (hm : m ≠ 0) :
    generated C v Lambda y p m ≠ 0 ↔ C ≠ 0 ∧ v ≠ 0 ∧ y ≠ 0 ∧ p ≠ 0 := by
  rw [generated_formula]
  simp [hLambda, hm, and_assoc]

/-- Exact zero-mode chart with nuL component 1; no canonical norm is asserted. -/
theorem mass_chart_formula (C v Lambda y d M m : ℂ) :
    generated C v Lambda y (-d/M) m = -(C*v*y*d/(Lambda*m*M)) := by
  rw [generated_formula]
  ring

theorem eliminated_pair {E : Type*} [AddCommGroup E] [Module ℂ E]
    (B : E →ₗ[ℂ] E →ₗ[ℂ] ℂ) (C v Lambda y p m : ℂ) (hm : m ≠ 0)
    (J K : E) :
    Math.TwoSourceQuadraticElimination.action B m (diquark C v Lambda) (-y*p) J K
      (Math.TwoSourceQuadraticElimination.leftSolution m (diquark C v Lambda) J)
      (Math.TwoSourceQuadraticElimination.rightSolution m (-y*p) K) =
      generated C v Lambda y p m * B J K :=
  Math.TwoSourceQuadraticElimination.on_shell B m _ _ hm J K

/-- Scalar cancellation control only; distinct physical sectors require transport. -/
theorem common_output_sum (CL CR v Lambda y p m : ℂ) :
    generated CL v Lambda y p m + generated CR v Lambda y p m =
      generated (CL+CR) v Lambda y p m := by
  simp only [generated_formula]
  ring

/-- A barred light source uses the conjugate of the holomorphic zero-mode coordinate. -/
def barProjection (d M : ℂ) := star (-d/M)

theorem barProjection_nonzero_iff (d M : ℂ) (hM : M ≠ 0) :
    barProjection d M ≠ 0 ↔ d ≠ 0 := by
  simp [barProjection, hM]

/-- Covariant Dirac Yukawa and heavy mixing kept distinct from the scalar vertex. -/
def covariant (C v Lambda y Y M m : ℂ) :=
  generated C v Lambda y (-star Y / star M) m

theorem covariant_formula (C v Lambda y Y M m : ℂ) :
    covariant C v Lambda y Y M m = -(C*v*y*star Y/(Lambda*m*star M)) := by
  unfold covariant
  rw [generated_formula]
  ring

theorem covariant_nonzero_iff (C v Lambda y Y M m : ℂ)
    (hLambda : Lambda ≠ 0) (hm : m ≠ 0) (hM : M ≠ 0) :
    covariant C v Lambda y Y M m ≠ 0 ↔ C ≠ 0 ∧ v ≠ 0 ∧ y ≠ 0 ∧ Y ≠ 0 := by
  unfold covariant
  rw [generated_nonzero_iff _ _ _ _ _ _ hLambda hm]
  simp [hM]

/-- w is the conjugate-Higgs VEV, so the unbarred Dirac entry is Y*star w. -/
theorem covariant_after_vev (C v Lambda y Y M m w : ℂ) :
    covariant C v Lambda y Y M m * w =
      generated C v Lambda y (barProjection (Y*star w) M) m := by
  simp only [covariant, barProjection, generated_formula, star_div₀, star_neg,
    star_mul, star_star]
  ring

/-- Physical scalar sign -m and the d,u-to-u,d color orientation cancel.
This is the on-shell identity for those actual signed source parameters. -/
theorem eliminated_oriented_pair {E : Type*} [AddCommGroup E] [Module ℂ E]
    (B : E →ₗ[ℂ] E →ₗ[ℂ] ℂ) (C v Lambda y p m : ℂ) (hm : m ≠ 0)
    (J K : E) :
    Math.TwoSourceQuadraticElimination.action B (-m) (diquark C v Lambda) (-y*p) (-J) K
      (Math.TwoSourceQuadraticElimination.leftSolution (-m) (diquark C v Lambda) (-J))
      (Math.TwoSourceQuadraticElimination.rightSolution (-m) (-y*p) K) =
      generated C v Lambda y p m * B J K := by
  rw [Math.TwoSourceQuadraticElimination.on_shell B (-m) _ _ (neg_ne_zero.mpr hm)]
  simp only [map_neg, LinearMap.neg_apply]
  unfold generated
  ring

/-- The epsilon component's four cancels the explicit UV Lagrangian quarter. -/
theorem uv_quarter (C v Lambda : ℂ) : C/(4*Lambda) * (4*v) = diquark C v Lambda := by
  unfold diquark
  ring

end
end GUT.PatiSalam.CoefficientParameters
