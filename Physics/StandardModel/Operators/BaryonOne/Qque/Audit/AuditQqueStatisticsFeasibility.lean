import Physics.StandardModel.Gauge.Tensors.ExplicitSMResidualTensor
import Math.RepresentationTheory.Symmetric.SymmetricInvariantPairing
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Bounded probes for the next qque milestone. These do not assemble an
equivariant Lorentz/SM/H operator on an arbitrary actual radical. -/

namespace Physics.QqueStatisticsFeasibility
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection
open scoped TensorProduct

section Flavor
variable {H A B D R : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup D] [Module ℂ D] [AddCommGroup R] [Module ℂ R]
  {a : Representation ℂ H A} {b : Representation ℂ H B}
  {d : Representation ℂ H D} {r : Representation ℂ H R}

/-- Reuse ONE Q projection in both slots before symmetrizing. -/
def symmetricCoefficient (sa : Split a r) (sb : Split b r) (sd : Split d r) :
    IntertwiningMap ((a.tprod a).tprod (b.dual.tprod d.dual))
      (Representation.trivial ℂ H ℂ) :=
  SymmetricInvariantPairing.coefficient sa sb sd

theorem symmetricCoefficient_apply (sa : Split a r) (sb : Split b r) (sd : Split d r)
    (x y : A) (u : Module.Dual ℂ B) (e : Module.Dual ℂ D) :
    symmetricCoefficient sa sb sd ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) =
      sb.dual.project u (sa.project x) * sd.dual.project e (sa.project y) +
      sb.dual.project u (sa.project y) * sd.dual.project e (sa.project x) := rfl

theorem symmetricCoefficient_swap (sa : Split a r) (sb : Split b r) (sd : Split d r)
    (x y : A) (u : Module.Dual ℂ B) (e : Module.Dual ℂ D) :
    symmetricCoefficient sa sb sd ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) =
      symmetricCoefficient sa sb sd ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  simp only [symmetricCoefficient_apply, add_comm]

theorem symmetricCoefficient_nonzero [Nontrivial R]
    (sa : Split a r) (sb : Split b r) (sd : Split d r) :
    symmetricCoefficient sa sb sd ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : R)
  obtain ⟨phi, hphi⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  have hv : symmetricCoefficient sa sb sd
      ((sa.embed x ⊗ₜ[ℂ] sa.embed x) ⊗ₜ[ℂ]
        (sb.dual.embed phi ⊗ₜ[ℂ] sd.dual.embed phi)) = 2 := by
    simp only [symmetricCoefficient_apply, sa.left_inv, sb.dual.left_inv,
      sd.dual.left_inv, hphi]
    norm_num
  intro hz
  rw [hz] at hv
  norm_num at hv
end Flavor

open SMEpsilonTensor

/-- Determinant-one complex 2x2 matrices suffice for either spinor epsilon.
The identification of the two actions with a Lorentz cover is not made here. -/
theorem spinor_epsilon_invariant (g : Matrix (Fin 2) (Fin 2) ℂ)
    (hg : g.det = 1) (x y : Fin 2 → ℂ) :
    eps2 (g.mulVec x) (g.mulVec y) = eps2 x y := eps2_invariant g hg x y

def componentContraction (a b c : Color) (i j s t u v : Weak) : ℂ :=
  eps3 a b c * eps2 i j * eps2 s t * eps2 u v

/-- Two gauge signs cancel; the left spinor sign remains. -/
theorem component_swap (a b c : Color) (i j s t u v : Weak) :
    componentContraction b a c j i t s u v =
      -componentContraction a b c i j s t u v := by
  simp only [componentContraction, eps3, eps2]
  ring

theorem component_one_generation :
    componentContraction (colorBasis 0) (colorBasis 1) (colorBasis 2)
      (weakBasis 0) (weakBasis 1) (weakBasis 0) (weakBasis 1)
      (weakBasis 0) (weakBasis 1) = 1 := by
  simp [componentContraction]

/- Four distinct component generators, not four generations:
Q_(color0,weak0,left0), Q_(color1,weak1,left1), u_(color2,right0), e_right1.
Setting all other one-generation components to zero leaves two Q orderings. -/
abbrev Components := Fin 4 → ℂ
def basis (i : Fin 4) : Components := Pi.single i 1
def ordered : Fin 4 → Components := ![basis 0, basis 1, basis 2, basis 3]
def exchanged : Fin 4 → Components := ![basis 1, basis 0, basis 2, basis 3]

def projectedOneGeneration : ⋀[ℂ]^4 Components :=
  exteriorPower.ιMulti ℂ 4 ordered - exteriorPower.ιMulti ℂ 4 exchanged

theorem projectedOneGeneration_from_components : projectedOneGeneration =
    componentContraction (colorBasis 0) (colorBasis 1) (colorBasis 2)
      (weakBasis 0) (weakBasis 1) (weakBasis 0) (weakBasis 1)
      (weakBasis 0) (weakBasis 1) • exteriorPower.ιMulti ℂ 4 ordered +
    componentContraction (colorBasis 1) (colorBasis 0) (colorBasis 2)
      (weakBasis 1) (weakBasis 0) (weakBasis 1) (weakBasis 0)
      (weakBasis 0) (weakBasis 1) • exteriorPower.ιMulti ℂ 4 exchanged := by
  rw [component_swap (colorBasis 0) (colorBasis 1) (colorBasis 2)
    (weakBasis 0) (weakBasis 1) (weakBasis 0) (weakBasis 1)
    (weakBasis 0) (weakBasis 1), component_one_generation]
  simp only [projectedOneGeneration, sub_eq_add_neg, one_smul]
  exact congrArg (fun z => exteriorPower.ιMulti ℂ 4 ordered + z)
    (neg_one_smul ℂ (exteriorPower.ιMulti ℂ 4 exchanged)).symm

def detector : (⋀[ℂ]^4 Components) →ₗ[ℂ] ℂ :=
  exteriorPower.alternatingMapLinearEquiv
    (Matrix.detRowAlternating : Components [⋀^Fin 4]→ₗ[ℂ] ℂ)

theorem projectedOneGeneration_detected : detector projectedOneGeneration = 2 := by
  simp only [projectedOneGeneration, map_sub, detector,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change Matrix.det _ - Matrix.det _ = 2
  have ho : ordered = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ordered, basis, Matrix.one_apply, Pi.single_apply, Fin.ext_iff]
  have hs : exchanged = (Matrix.of ordered).submatrix (Equiv.swap 0 1) id := by
    funext i
    fin_cases i <;> rfl
  change Matrix.det ordered - Matrix.det exchanged = 2
  rw [hs, Matrix.det_permute]
  change Matrix.det ordered - _ * Matrix.det ordered = 2
  rw [ho]
  norm_num

theorem projectedOneGeneration_nonzero : projectedOneGeneration ≠ 0 := by
  intro hz
  have h := projectedOneGeneration_detected
  rw [hz, map_zero] at h
  norm_num at h

/-- The same exterior API kills a genuinely repeated component. -/
theorem repeated_component_zero :
    exteriorPower.ιMulti ℂ 4 ![basis 0, basis 0, basis 2, basis 3] = 0 := by
  apply (exteriorPower.ιMulti ℂ 4).map_eq_zero_of_eq _ (i := 0) (j := 1)
  · rfl
  · decide

end
end Physics.QqueStatisticsFeasibility

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Statistics probe imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.QqueStatisticsFeasibility.symmetricCoefficient,
    ``Physics.QqueStatisticsFeasibility.symmetricCoefficient_swap,
    ``Physics.QqueStatisticsFeasibility.symmetricCoefficient_nonzero,
    ``Physics.QqueStatisticsFeasibility.spinor_epsilon_invariant,
    ``Physics.QqueStatisticsFeasibility.component_swap,
    ``Physics.QqueStatisticsFeasibility.component_one_generation,
    ``Physics.QqueStatisticsFeasibility.projectedOneGeneration_from_components,
    ``Physics.QqueStatisticsFeasibility.projectedOneGeneration_detected,
    ``Physics.QqueStatisticsFeasibility.projectedOneGeneration_nonzero,
    ``Physics.QqueStatisticsFeasibility.repeated_component_zero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Statistics probe: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Qque statistics feasibility: {declarations.length} strict axiom checks passed"
