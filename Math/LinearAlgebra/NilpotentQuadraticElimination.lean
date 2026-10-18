import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

/-! Exact inversion of a finite nilpotent quadratic perturbation.
No degree truncation or convergence assumption. -/
namespace Math.NilpotentQuadraticElimination
set_option autoImplicit false
noncomputable section
variable {k E F : Type*} [Field k] [AddCommGroup E] [Module k E]
  [AddCommGroup F] [Module k F]

def inverse (T : Module.End k E) (N : ℕ) : Module.End k E :=
  ∑ i ∈ Finset.range N, T^i

theorem inverse_left (T : Module.End k E) (N : ℕ) (hT : T^N = 0) :
    inverse T N * (1-T) = 1 := by
  simpa [inverse, hT] using geom_sum_mul_neg T N

theorem inverse_right (T : Module.End k E) (N : ℕ) (hT : T^N = 0) :
    (1-T) * inverse T N = 1 := by
  simpa [inverse, hT] using mul_neg_geom_sum T N

def solution (T : Module.End k E) (N : ℕ) (s : E) : E := inverse T N s

theorem source_equation (T : Module.End k E) (N : ℕ) (hT : T^N = 0) (s : E) :
    solution T N s - T (solution T N s) = s := by
  have h := LinearMap.congr_fun (inverse_right T N hT) s
  simpa [solution, Module.End.mul_apply] using h

theorem unique (T : Module.End k E) (N : ℕ) (hT : T^N = 0) (s x : E)
    (hx : x-T x = s) : x = solution T N s := by
  have h := LinearMap.congr_fun (inverse_left T N hT) x
  change inverse T N (x-T x) = x at h
  rw [hx] at h
  exact h.symm

/-- An algebra-valued symmetric quadratic action; B can encode odd-field
multiplication and its antisymmetric spin kernel. -/
def action (B : E →ₗ[k] E →ₗ[k] F) (L : E →ₗ[k] F) (c : F) (x : E) : F :=
  (1/2 : k) • B x x + L x + c

def Stationary (B : E →ₗ[k] E →ₗ[k] F) (L : E →ₗ[k] F) (x : E) : Prop :=
  ∀ y, B x y + L y = 0

variable [NeZero (2 : k)]

theorem shifted_action (B : E →ₗ[k] E →ₗ[k] F) (L : E →ₗ[k] F) (c : F)
    (hB : ∀ x y, B x y = B y x) (x : E) (hx : Stationary B L x) (y : E) :
    action B L c (x+y) = action B L c x + (1/2 : k) • B y y := by
  have hxy : L y = -(B x y) := eq_neg_of_add_eq_zero_right (hx y)
  simp only [action, map_add, LinearMap.add_apply, hB y x, hxy, smul_add]
  match_scalars <;> (field_simp <;> ring)

theorem on_shell (B : E →ₗ[k] E →ₗ[k] F) (L : E →ₗ[k] F) (c : F)
    (x : E) (hx : Stationary B L x) :
    action B L c x = (1/2 : k) • L x + c := by
  have hxx : B x x = -(L x) := eq_neg_of_add_eq_zero_left (hx x)
  simp only [action, hxx, smul_neg]
  match_scalars <;> (field_simp <;> ring)

omit [NeZero (2 : k)] in
/-- Prove the concrete first variation factors through 1-T, rather than
assuming stationarity of an independently supplied candidate. -/
theorem solution_stationary (T : Module.End k E) (N : ℕ) (hT : T^N = 0)
    (s : E) (B : E →ₗ[k] E →ₗ[k] F) (L : E →ₗ[k] F)
    (C : E →ₗ[k] E →ₗ[k] F)
    (hfactor : ∀ x y, B x y + L y = C (x-T x-s) y) :
    Stationary B L (solution T N s) := by
  intro y
  rw [hfactor, source_equation T N hT, sub_self, map_zero, LinearMap.zero_apply]

omit [NeZero (2 : k)] in
/-- Uniqueness follows from nondegeneracy of the unperturbed kernel C. -/
theorem stationary_unique (T : Module.End k E) (N : ℕ) (hT : T^N = 0)
    (s : E) (B : E →ₗ[k] E →ₗ[k] F) (L : E →ₗ[k] F)
    (C : E →ₗ[k] E →ₗ[k] F)
    (hfactor : ∀ x y, B x y + L y = C (x-T x-s) y)
    (hC : ∀ z, (∀ y, C z y = 0) → z = 0)
    (x : E) (hx : Stationary B L x) : x = solution T N s := by
  apply unique T N hT s x
  apply sub_eq_zero.mp
  apply hC
  intro y
  rw [← hfactor]
  exact hx y

/-- Exact all-order on-shell action at the finite inverse solution. -/
theorem eliminated_action (T : Module.End k E) (N : ℕ) (hT : T^N = 0)
    (s : E) (B : E →ₗ[k] E →ₗ[k] F) (L : E →ₗ[k] F) (c : F)
    (C : E →ₗ[k] E →ₗ[k] F)
    (hfactor : ∀ x y, B x y + L y = C (x-T x-s) y) :
    action B L c (solution T N s) = (1/2 : k) • L (solution T N s) + c :=
  on_shell B L c _ (solution_stationary T N hT s B L C hfactor)

end
end Math.NilpotentQuadraticElimination
