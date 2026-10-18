import Math.LieGroups.E6.Minuscule.TorusFundamentalGroup
import Lean.Util.CollectAxioms

/-! Arbitrary torus-loop contractions and the induced map, with winding,
basepoint and nontrivial group-inclusion controls. -/

set_option autoImplicit false

namespace Math.E6.Audit.TorusLoops

noncomputable section

open Minuscule unitInterval

example (p : Path (1 : Torus.Point) 1) :
    (Torus.loopImage p).Homotopy (Path.refl 1) := Torus.loopContraction p

example (p : Path (1 : Torus.Point) 1) (u : I) : Torus.loopContraction p (u, 0) = 1 :=
  Path.Homotopy.source _ _

example (p : Path (1 : Torus.Point) 1) (u : I) : Torus.loopContraction p (u, 1) = 1 :=
  Path.Homotopy.target _ _

example (i : Fin 6) (u : ℝ) : Coroot.filling i u (-3) = 1 := by
  simpa using Coroot.filling_integer i u (-3)

example (i : Fin 6) (u : ℝ) : Coroot.filling i u 17 = 1 := by
  simpa using Coroot.filling_integer i u 17

private def windingLoop (n : Fin 6 → ℤ) : Path (1 : Torus.Point) 1 where
  toFun s := Torus.phase fun i => 2 * Real.pi * (n i : ℝ) * (s : ℝ)
  continuous_toFun := by unfold Torus.phase; fun_prop
  source' := by ext i; simp [Torus.phase]
  target' := by ext i; simp [Torus.phase, Circle.exp_two_pi_mul_int]

-- All six windings may vary independently, with either sign and no bound.
example (n : Fin 6 → ℤ) :
    (Torus.loopImage (windingLoop n)).Homotopic (Path.refl 1) :=
  Torus.loopImage_nullhomotopic _

example (c : FundamentalGroup Torus.Point 1) : Torus.fundamentalMap c = 1 :=
  Torus.fundamentalMap_apply_eq_one c

example : Torus.fundamentalMap.range = ⊥ := Torus.fundamentalMap_range

-- A trivial induced fundamental-group map is not a trivial group inclusion.
example : Torus.hom ≠ 1 := by
  intro h
  have he : Torus.phase (Pi.single (0 : Fin 6) Real.pi) = 1 :=
    Torus.hom_injective (by rw [h]; rfl)
  exact Circle.exp_pi_ne_one (by simpa [Torus.phase] using congrFun he 0)

end

end Math.E6.Audit.TorusLoops

run_cmd do
  let declarations := [
    ``Math.CircleLoopLift.angle,
    ``Math.CircleLoopLift.angle_zero,
    ``Math.CircleLoopLift.exp_angle,
    ``Math.CircleLoopLift.angle_one_period,
    ``Math.CircleLoopLift.turns,
    ``Math.CircleLoopLift.turns_zero,
    ``Math.CircleLoopLift.exp_turns,
    ``Math.CircleLoopLift.turns_one_integer,
    ``Math.E6.Minuscule.Coroot.hLine_int_mul,
    ``Math.E6.Minuscule.Coroot.filling_integer,
    ``Math.E6.Minuscule.Torus.phase_single,
    ``Math.E6.Minuscule.Torus.hom_coordinate_product,
    ``Math.E6.Minuscule.Torus.coordinateLoop,
    ``Math.E6.Minuscule.Torus.loopImage,
    ``Math.E6.Minuscule.Torus.loopFilling_continuous,
    ``Math.E6.Minuscule.Torus.loopFilling_start,
    ``Math.E6.Minuscule.Torus.loopFilling_finish,
    ``Math.E6.Minuscule.Torus.loopFilling_source,
    ``Math.E6.Minuscule.Torus.loopFilling_target,
    ``Math.E6.Minuscule.Torus.loopContraction,
    ``Math.E6.Minuscule.Torus.loopImage_nullhomotopic,
    ``Math.E6.Minuscule.Torus.fundamentalMap,
    ``Math.E6.Minuscule.Torus.fundamentalMap_loop,
    ``Math.E6.Minuscule.Torus.fundamentalMap_apply_eq_one,
    ``Math.E6.Minuscule.Torus.fundamentalMap_trivial,
    ``Math.E6.Minuscule.Torus.fundamentalMap_range]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6 torus loops: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6 torus loops: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6 torus loops: checked {declarations.length} declarations"
