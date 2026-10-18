import Math.LieGroups.E6.Minuscule.TorusCentralizer
import Math.LieGroups.E6.Minuscule.ExactCenter
import Lean.Util.CollectAxioms

/-! Actual torus, full period lattice and self-centralizer checks.
None of these statements supplies a fundamental-group comparison. -/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

example : Topology.IsClosedEmbedding Torus.hom := Torus.hom_closedEmbedding

example (t : Fin 6 → ℝ) : exp (Torus.direction t : Matrix27) = 1 ↔
    ∃ m : Fin 6 → ℤ, ∀ i, t i = (m i : ℝ) * (2 * Real.pi) :=
  Torus.exp_direction_eq_one_iff t

-- A half period is not silently identified with a full period.
example (i : Fin 6) : Torus.hom (Torus.phase (Pi.single i Real.pi)) ≠ 1 := by
  intro h
  have he : Torus.phase (Pi.single i Real.pi) = 1 := Torus.hom_injective (by simpa using h)
  have hi := congrFun he i
  exact Circle.exp_pi_ne_one (by simpa [Torus.phase] using hi)

example (g : compactIdentityComponent) (d : Fin 27 → Circle)
    (hd : compactMatrix g = Matrix.diagonal (fun a => (d a : ℂ))) :
    g = Torus.hom (Torus.recover d) := Torus.diagonal_reconstruction g d hd

example : Subgroup.centralizer (Torus.subgroup : Set compactIdentityComponent) = Torus.subgroup :=
  Torus.centralizer_eq

example (A : Subgroup compactIdentityComponent) (hT : Torus.subgroup ≤ A)
    (hA : ∀ g ∈ A, ∀ h ∈ A, Commute g h) : A = Torus.subgroup := Torus.maximal_abelian A hT hA

example : centralScalar3 ∈ Torus.subgroup := by
  apply Torus.mem_subgroup_of_diagonal
  rw [centralScalar3_matrix]
  ext i j
  by_cases h : i = j <;> simp [h]

example : centralScalar27 ∉ compactIdentityComponent := centralScalar27_not_mem

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.E6.Minuscule.Torus.powerMap_mul,
    ``Math.E6.Minuscule.Torus.seed_inverse_left,
    ``Math.E6.Minuscule.Torus.seed_inverse_right,
    ``Math.E6.Minuscule.Torus.recover_weights,
    ``Math.E6.Minuscule.Torus.weights_recover_seed,
    ``Math.E6.Minuscule.Torus.weights_injective,
    ``Math.E6.Minuscule.Torus.direction_matrix,
    ``Math.E6.Minuscule.Torus.exp_direction,
    ``Math.E6.Minuscule.Torus.hom,
    ``Math.E6.Minuscule.Torus.hom_matrix,
    ``Math.E6.Minuscule.Torus.hom_injective,
    ``Math.E6.Minuscule.Torus.hom_continuous,
    ``Math.E6.Minuscule.Torus.hom_closedEmbedding,
    ``Math.E6.Minuscule.Torus.subgroup_isCompact,
    ``Math.E6.Minuscule.Torus.subgroup_isConnected,
    ``Math.E6.Minuscule.Torus.hom_phase,
    ``Math.E6.Minuscule.Torus.exp_direction_eq_one_iff,
    ``Math.E6.Minuscule.Torus.predecessors_lt,
    ``Math.E6.Minuscule.Torus.coordinateOrder_surjective,
    ``Math.E6.Minuscule.Torus.cubic_tripleMask,
    ``Math.E6.Minuscule.Torus.diagonal_triple_relation,
    ``Math.E6.Minuscule.Torus.eq_of_triples,
    ``Math.E6.Minuscule.Torus.diagonal_reconstruction,
    ``Math.E6.Minuscule.Torus.centralizer_commutes_cartan,
    ``Math.E6.Minuscule.Torus.centralizer_diagonal,
    ``Math.E6.Minuscule.Torus.diagonal_norm,
    ``Math.E6.Minuscule.Torus.mem_subgroup_of_diagonal,
    ``Math.E6.Minuscule.Torus.centralizer_eq,
    ``Math.E6.Minuscule.Torus.maximal_abelian]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6 compact torus: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6 compact torus: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6 compact torus: checked {declarations.length} declarations"
