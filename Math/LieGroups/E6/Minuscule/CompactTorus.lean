import Math.LieGroups.E6.Minuscule.TorusCoordinates
import Math.LieGroups.E6.Minuscule.CompactLieGroup

/-! The actual six-circle subgroup and its exact Cartan exponential kernel.
Global simple connectedness is not asserted by this period calculation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Math.E6.Minuscule.Torus

noncomputable section

open TauCeti.DynkinType NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

def matrix (z : Point) : Matrix27 := Matrix.diagonal fun a => (weights z a : ℂ)

def direction (t : Fin 6 → ℝ) : compactMatrixLieAlgebra :=
  ∑ i : Fin 6, t i • compactMatrixEquiv (compactGeneratorElement 2 i)

theorem direction_matrix (t : Fin 6 → ℝ) : (direction t : Matrix27) =
    Matrix.diagonal (fun a => (∑ i, (e6MinusculeWeight a i : ℂ) * (t i : ℂ)) * Complex.I) := by
  ext a b
  change (∑ i : Fin 6, t i • compactH i) a b = _
  by_cases h : a = b
  · subst b
    simp [compactH, cartan, Matrix.sum_apply, RCLike.real_smul_eq_coe_mul,
      Finset.mul_sum, mul_comm, mul_left_comm]
  · simp [compactH, cartan, h, Matrix.sum_apply]

def phase (t : Fin 6 → ℝ) : Point := fun i => Circle.exp (t i)

theorem weights_phase (t : Fin 6 → ℝ) (a : Fin 27) :
    weights (phase t) a = Circle.exp (∑ i, (e6MinusculeWeight a i : ℝ) * t i) := by
  change (∏ i, Circle.exp (t i) ^ e6MinusculeWeight a i) = _
  simp only [← Circle.exp_intCast_mul]
  exact (map_sum Circle.expHom _ _).symm

theorem exp_direction (t : Fin 6 → ℝ) : exp (direction t : Matrix27) = matrix (phase t) := by
  rw [direction_matrix, Matrix.exp_diagonal]
  apply congrArg Matrix.diagonal
  funext a
  rw [Pi.coe_exp]
  change exp ((∑ i, (e6MinusculeWeight a i : ℂ) * (t i : ℂ)) * Complex.I) = _
  rw [weights_phase, Circle.coe_exp]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  exact (congrFun Complex.exp_eq_exp_ℂ _).symm

private def angles (z : Point) : Fin 6 → ℝ := fun i => Complex.arg (z i : ℂ)

private theorem phase_angles (z : Point) : phase (angles z) = z := by
  funext i; exact Circle.exp_arg (z i)

private theorem matrix_exp (X : compactMatrixLieAlgebra) :
    compactMatrix (compactExp X) = exp (X : Matrix27) := compactExp_coe X

private def element (z : Point) : compactIdentityComponent := compactExp (direction (angles z))

private theorem element_matrix (z : Point) : compactMatrix (element z) = matrix z := by
  rw [element, matrix_exp, exp_direction, phase_angles]

def hom : Point →* compactIdentityComponent where
  toFun := element
  map_one' := by
    apply compactMatrix_injective
    rw [element_matrix, compactMatrix_one]
    simp [matrix, weights, powerMap]
  map_mul' z w := by
    apply compactMatrix_injective
    simp only [compactMatrix_mul, element_matrix]
    simp [matrix, weights, powerMap, Matrix.diagonal_mul_diagonal, mul_zpow,
      Finset.prod_mul_distrib, Circle.coe_mul]

@[simp] theorem hom_matrix (z : Point) : compactMatrix (hom z) = matrix z := element_matrix z

theorem hom_injective : Function.Injective hom := by
  intro z w he
  apply weights_injective
  funext a
  apply Circle.coe_injective
  have h := congrArg (fun g => compactMatrix g a a) he
  simpa only [hom_matrix, matrix, Matrix.diagonal_apply_eq] using h

theorem hom_continuous : Continuous hom := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  change Continuous (fun z => compactMatrix (hom z))
  simp only [hom_matrix, matrix]
  have hw : Continuous weights := by unfold weights powerMap; fun_prop
  have hd : Continuous (fun d : Fin 27 → Circle => Matrix.diagonal fun a => (d a : ℂ)) := by
    fun_prop
  exact hd.comp hw

def continuousHom : Point →ₜ* compactIdentityComponent := ⟨hom, hom_continuous⟩

theorem hom_closedEmbedding : Topology.IsClosedEmbedding hom :=
  hom_continuous.isClosedEmbedding hom_injective

def subgroup : Subgroup compactIdentityComponent := hom.range

theorem subgroup_isCompact : IsCompact (subgroup : Set compactIdentityComponent) :=
  isCompact_range hom_continuous

theorem subgroup_isConnected : IsConnected (subgroup : Set compactIdentityComponent) :=
  isConnected_range hom_continuous

theorem hom_phase (t : Fin 6 → ℝ) : hom (phase t) = compactExp (direction t) := by
  apply compactMatrix_injective
  rw [hom_matrix, matrix_exp, exp_direction]

theorem exp_direction_eq_one_iff (t : Fin 6 → ℝ) :
    exp (direction t : Matrix27) = 1 ↔
      ∃ m : Fin 6 → ℤ, ∀ i, t i = (m i : ℝ) * (2 * Real.pi) := by
  have h : exp (direction t : Matrix27) = 1 ↔ phase t = 1 := by
    rw [← matrix_exp, ← hom_phase]
    change compactMatrix (hom (phase t)) = compactMatrix 1 ↔ _
    rw [compactMatrix_injective.eq_iff, ← map_one hom, hom_injective.eq_iff]
  rw [h, funext_iff]
  simp only [phase, Pi.one_apply, Circle.exp_eq_one]
  exact Classical.skolem

end

end Math.E6.Minuscule.Torus
