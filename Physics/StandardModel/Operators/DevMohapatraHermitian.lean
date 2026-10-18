import Physics.StandardModel.Operators.DevMohapatraExternalLeg
import Mathlib.Algebra.Star.Module

/-! Actual Hermitian conjugation in a supplied complex star algebra.
Exact scalar elimination retains the conjugate and mixed channels. -/
namespace GUT.DevMohapatraHermitian
set_option autoImplicit false
noncomputable section
open Math.AlgebraValuedQuadraticElimination
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

def vertex (a b : ℂ) (U D x y : R) : R := a • (U*y) + b • (x*D)

def scalarAction (m a b : ℂ) (U D x : R) : R :=
  m • (x * star x) + vertex a b U D x (star x) +
    star (vertex a b U D x (star x))

def leftSource (a b : ℂ) (U D : R) : R := a • U + star b • star D
def rightSource (a b : ℂ) (U D : R) : R := b • D + star a • star U

/-- Complexification permits independent scalar variables, with literal
conjugate coefficients and vertices. The Hermitian slice is y = star x. -/
def complexifiedScalar (m a b : ℂ) (U D x y : R) : R :=
  pairedAction m 1 1 (leftSource a b U D) (rightSource a b U D) x y

theorem sources_conjugate (a b : ℂ) (U D : R) :
    star (leftSource a b U D) = rightSource a b U D := by
  simp [leftSource, rightSource, add_comm]

theorem scalar_dictionary (m a b : ℂ) (U D x : R) :
    scalarAction m a b U D x = complexifiedScalar m a b U D x (star x) := by
  simp [scalarAction, vertex, complexifiedScalar, pairedAction, leftSource,
    rightSource, star_add, star_mul, smul_add, add_mul, mul_add]
  abel

theorem scalar_hermitian (m a b : ℂ) (hm : star m = m) (U D x : R) :
    star (scalarAction m a b U D x) = scalarAction m a b U D x := by
  simp only [scalarAction, star_add, star_smul, star_mul, star_star, hm]
  abel

def massAction (M : ℂ) (n : Fin 2 → R) : R :=
  -M • (n 0*n 1) + star (-M • (n 0*n 1))

theorem mass_hermitian (M : ℂ) (n : Fin 2 → R) :
    star (massAction M n) = massAction M n := by
  simp [massAction, add_comm]

/-- Anti-multiplicativity reverses the barred spin order. -/
theorem mass_dictionary (M : ℂ) (n : Fin 2 → R) :
    massAction M n = -M • (n 0*n 1) - star M • (star (n 1)*star (n 0)) := by
  simp [massAction, star_smul, star_mul, sub_eq_add_neg, neg_smul]

def scalarEffective (m a b : ℂ) (U D : R) : R :=
  -(1/m) • (leftSource a b U D * rightSource a b U D)

omit [StarModule ℂ R] in
theorem scalar_on_shell (m a b : ℂ) (hm : m ≠ 0) (U D : R) :
    complexifiedScalar m a b U D
      (solution m 1 (leftSource a b U D))
      (solution m 1 (rightSource a b U D)) = scalarEffective m a b U D := by
  simpa [complexifiedScalar, scalarEffective] using
    paired_on_shell m 1 1 hm (leftSource a b U D) (rightSource a b U D)

/-- Both scalar solutions lie on the Hermitian slice for real m. -/
theorem solutions_conjugate (m a b : ℂ) (hm : star m = m) (U D : R) :
    star (solution m 1 (leftSource a b U D)) =
      solution m 1 (rightSource a b U D) := by
  simp [solution, star_smul, hm, sources_conjugate]

theorem hermitian_on_shell (m a b : ℂ) (hm : m ≠ 0) (hmreal : star m = m)
    (U D : R) :
    scalarAction m a b U D (solution m 1 (leftSource a b U D)) =
      scalarEffective m a b U D := by
  rw [scalar_dictionary, solutions_conjugate m a b hmreal, scalar_on_shell m a b hm]

theorem effective_hermitian (m a b : ℂ) (hm : star m = m) (U D : R) :
    star (scalarEffective m a b U D) = scalarEffective m a b U D := by
  have hr : star (rightSource a b U D) = leftSource a b U D := by
    rw [← sources_conjugate, star_star]
  simp [scalarEffective, star_smul, star_mul, hm, hr, sources_conjugate]

omit [StarModule ℂ R] in
/-- The mixed terms are retained, rather than dropped by a chiral truncation. -/
theorem effective_expansion (m a b : ℂ) (U D : R) :
    scalarEffective m a b U D =
      -(a*b/m) • (U*D) - (a*star a/m) • (U*star U) -
      (star b*b/m) • (star D*D) - (star b*star a/m) • (star D*star U) := by
  simp only [scalarEffective, leftSource, rightSource, add_mul, mul_add,
    smul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  module

omit [StarModule ℂ R] in
/-- Projection of the exact scalar effective action; no heavy solution is assumed. -/
theorem effective_projection {S : Type*} [Ring S] [Algebra ℂ S]
    (f : R →ₐ[ℂ] S) (m a b : ℂ) (U D : R)
    (hU : f (star U) = 0) (hD : f (star D) = 0) :
    f (scalarEffective m a b U D) = -(a*b/m) • (f U*f D) := by
  rw [effective_expansion]
  simp [hU, hD]

/-- One scalar quadratic term per color, and literal H.c. for every vertex
and the chiral Majorana mass. U may depend on n. -/
def action (m M a b : ℂ) (n : Fin 2 → R) (U D x : Fin 3 → R) : R :=
  massAction M n + ∑ i, scalarAction m a b (U i) (D i) (x i)

def effectiveAction (m M a b : ℂ) (n : Fin 2 → R) (U D : Fin 3 → R) : R :=
  massAction M n + ∑ i, scalarEffective m a b (U i) (D i)

theorem action_hermitian (m M a b : ℂ) (hm : star m = m)
    (n : Fin 2 → R) (U D x : Fin 3 → R) :
    star (action m M a b n U D x) = action m M a b n U D x := by
  simp [action, star_sum, mass_hermitian, scalar_hermitian m a b hm]

theorem action_scalar_on_shell (m M a b : ℂ) (hm : m ≠ 0)
    (hmreal : star m = m) (n : Fin 2 → R) (U D : Fin 3 → R) :
    action m M a b n U D
      (fun i => solution m 1 (leftSource a b (U i) (D i))) =
      effectiveAction m M a b n U D := by
  simp only [action, effectiveAction, hermitian_on_shell m a b hm hmreal]

theorem action_effective_hermitian (m M a b : ℂ) (hm : star m = m)
    (n : Fin 2 → R) (U D : Fin 3 → R) :
    star (effectiveAction m M a b n U D) = effectiveAction m M a b n U D := by
  simp [effectiveAction, star_sum, mass_hermitian, effective_hermitian m a b hm]

end
end GUT.DevMohapatraHermitian
