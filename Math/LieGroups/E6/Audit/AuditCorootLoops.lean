import Math.LieGroups.E6.Minuscule.CorootLoops
import Lean.Util.CollectAxioms

/-! Actual based contractions, with nonconstant-loop and fixed-endpoint
controls. This audit does not assert simple connectedness of the group. -/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule unitInterval

example (i : Fin 6) : (Coroot.loop i).Homotopy (Path.refl 1) := Coroot.contraction i

example (i : Fin 6) (u : I) : Coroot.contraction i (u, 0) = 1 :=
  Path.Homotopy.source _ _

example (i : Fin 6) (u : I) : Coroot.contraction i (u, 1) = 1 :=
  Path.Homotopy.target _ _

example (i : Fin 6) (s : I) : Coroot.loop i s =
    Torus.hom (Torus.phase (Pi.single i (2 * Real.pi * (s : ℝ)))) :=
  Coroot.hLine_torus i _

-- The starting loop is not the constant loop supplied as its own contraction.
example (i : Fin 6) : Coroot.loop i ⟨1 / 2, by norm_num⟩ ≠ 1 := by
  change Coroot.hLine i (2 * Real.pi * (1 / 2)) ≠ 1
  rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring, Coroot.hLine_torus]
  intro h
  have he : Torus.phase (Pi.single i Real.pi) = 1 := Torus.hom_injective (by simpa using h)
  exact Circle.exp_pi_ne_one (by simpa [Torus.phase] using congrFun he i)

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.RotationExponential.rotation_derivative,
    ``Math.RotationExponential.hasDerivAt_rotation,
    ``Math.RotationExponential.exp_eq_rotation,
    ``Math.E6.Minuscule.Coroot.x_cube,
    ``Math.E6.Minuscule.Coroot.cartan_cube,
    ``Math.E6.Minuscule.Coroot.x_square,
    ``Math.E6.Minuscule.Coroot.quarter_anticommutes,
    ``Math.E6.Minuscule.Coroot.h_cube,
    ``Math.E6.Minuscule.Coroot.h_square,
    ``Math.E6.Minuscule.Coroot.exp_h_pi,
    ``Math.E6.Minuscule.Coroot.exp_h_two_pi,
    ``Math.E6.Minuscule.Coroot.exp_x_half_pi,
    ``Math.E6.Minuscule.Coroot.half_period_commutes,
    ``Math.E6.Minuscule.Coroot.quarter_turn,
    ``Math.E6.Minuscule.Coroot.line_add,
    ``Math.E6.Minuscule.Coroot.hLine_torus,
    ``Math.E6.Minuscule.Coroot.hLine_pi_square,
    ``Math.E6.Minuscule.Coroot.hLine_pi_commutes,
    ``Math.E6.Minuscule.Coroot.hLine_quarter_turn,
    ``Math.E6.Minuscule.Coroot.loop,
    ``Math.E6.Minuscule.Coroot.filling_continuous,
    ``Math.E6.Minuscule.Coroot.filling_start,
    ``Math.E6.Minuscule.Coroot.filling_finish,
    ``Math.E6.Minuscule.Coroot.filling_source,
    ``Math.E6.Minuscule.Coroot.filling_target,
    ``Math.E6.Minuscule.Coroot.contraction,
    ``Math.E6.Minuscule.Coroot.loop_nullhomotopic]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6 coroot loops: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6 coroot loops: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6 coroot loops: checked {declarations.length} declarations"
