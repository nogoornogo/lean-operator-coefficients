import Math.RepresentationTheory.SixSlotAlternation
import Physics.FieldTheory.Spinor.WeylSpinor
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Mathlib.LinearAlgebra.Multilinear.Curry

open Math

/-!
# An explicit all-right-handed six-quark coefficient

This file constructs the conventional `AAS` color tensor for the all-right-
handed `uudddd` sector, pairs the three right-handed Weyl diquarks, and descends
the resulting ordered invariant to the sixth exterior power. No basis
completeness, matching, QCD matrix element or oscillation rate is asserted.
-/

namespace GUT.DeltaBTwoSixQuark

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section

open Representation SMEpsilonTensor ExternalInvariantTensor
open scoped TensorProduct

abbrev Spin := WeylSpinor.Space
abbrev RightQuark := Color ⊗[ℂ] Spin
abbrev ColorPair := Color ⊗[ℂ] Color

private def evalEmpty {V : Type*} [AddCommGroup V] [Module ℂ V] :
    MultilinearMap ℂ (fun _ : Fin 0 => V) ℂ →ₗ[ℂ] ℂ where
  toFun f := f Fin.elim0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def curryOne {V : Type*} [AddCommGroup V] [Module ℂ V] :
    MultilinearMap ℂ (fun _ : Fin 1 => V) ℂ →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ evalEmpty).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 1 => V) ℂ).toLinearMap

private def curryTwo {V : Type*} [AddCommGroup V] [Module ℂ V] :
    MultilinearMap ℂ (fun _ : Fin 2 => V) ℂ →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ curryOne).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 2 => V) ℂ).toLinearMap

private def curryThree {V : Type*} [AddCommGroup V] [Module ℂ V] :
    MultilinearMap ℂ (fun _ : Fin 3 => V) ℂ →ₗ[ℂ]
      V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ curryTwo).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 3 => V) ℂ).toLinearMap

private def curryFour {V : Type*} [AddCommGroup V] [Module ℂ V] :
    MultilinearMap ℂ (fun _ : Fin 4 => V) ℂ →ₗ[ℂ]
      V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ curryThree).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 4 => V) ℂ).toLinearMap

private def curryFive {V : Type*} [AddCommGroup V] [Module ℂ V] :
    MultilinearMap ℂ (fun _ : Fin 5 => V) ℂ →ₗ[ℂ]
      V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ curryFour).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 5 => V) ℂ).toLinearMap

private def currySix {V : Type*} [AddCommGroup V] [Module ℂ V] :
    MultilinearMap ℂ (fun _ : Fin 6 => V) ℂ →ₗ[ℂ]
      V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ curryFive).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 6 => V) ℂ).toLinearMap

/-- The color tensor `T^{AAS}` in the slot convention
`(u_i d_j)(u_k d_l)(d_m d_n)`, matching Eq. (3) of arXiv:1901.07519. -/
def colorAASMulti : MultilinearMap ℂ (fun _ : Fin 6 => Color) ℂ :=
  MultilinearMap.mk'
    (fun v => eps3 (v 0) (v 1) (v 4) * eps3 (v 2) (v 3) (v 5) +
      eps3 (v 0) (v 1) (v 5) * eps3 (v 2) (v 3) (v 4))
    (by intro v i x y; fin_cases i <;>
      simp [Function.update, eps3, add_mul, mul_add] <;> ring)
    (by intro v i c x; fin_cases i <;>
      simp [Function.update, eps3] <;> ring)

private def pairLift {X : Type*} [AddCommMonoid X] [Module ℂ X] :
    (Color →ₗ[ℂ] Color →ₗ[ℂ] X) →ₗ[ℂ] ColorPair →ₗ[ℂ] X :=
  (TensorProduct.lift.equiv (.id ℂ) Color Color X).toLinearMap

private def colorFirstPair : ColorPair →ₗ[ℂ]
    Color →ₗ[ℂ] Color →ₗ[ℂ] Color →ₗ[ℂ] Color →ₗ[ℂ] ℂ :=
  pairLift (X := Color →ₗ[ℂ] Color →ₗ[ℂ] Color →ₗ[ℂ] Color →ₗ[ℂ] ℂ)
    (currySix colorAASMulti)

private def colorSecondPair : ColorPair →ₗ[ℂ] ColorPair →ₗ[ℂ]
    Color →ₗ[ℂ] Color →ₗ[ℂ] ℂ where
  toFun p := pairLift (X := Color →ₗ[ℂ] Color →ₗ[ℂ] ℂ) (colorFirstPair p)
  map_add' p q := by ext c d e f; simp
  map_smul' z p := by ext c d e f; simp

private def colorThirdPair : ColorPair →ₗ[ℂ] ColorPair →ₗ[ℂ] ColorPair →ₗ[ℂ] ℂ where
  toFun p :=
    { toFun := fun q => pairLift (X := ℂ) (colorSecondPair p q)
      map_add' := by intro q r; ext e f; simp
      map_smul' := by intro z q; ext e f; simp }
  map_add' p q := by ext r e f; simp
  map_smul' z p := by ext r e f; simp

/-- `T^{AAS}` as a linear functional on three ordered color pairs. -/
def colorAAS : ((ColorPair ⊗[ℂ] ColorPair) ⊗[ℂ] ColorPair) →ₗ[ℂ] ℂ :=
  TensorProduct.lift (TensorProduct.lift colorThirdPair)

@[simp] theorem colorAAS_tmul (a b c d e f : Color) :
    colorAAS (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) ⊗ₜ[ℂ] (e ⊗ₜ[ℂ] f)) =
      eps3 a b e * eps3 c d f + eps3 a b f * eps3 c d e := by
  simp [colorAAS, colorThirdPair, colorSecondPair, colorFirstPair, pairLift,
    currySix, curryFive, curryFour, curryThree, curryTwo, curryOne, evalEmpty,
    colorAASMulti]
  change eps3 a b e * eps3 c d f + eps3 a b f * eps3 c d e =
    eps3 a b e * eps3 c d f + eps3 a b f * eps3 c d e
  rfl

/-- Contract a right-handed Weyl pair, retaining its ordered color pair. -/
def diquark : (RightQuark ⊗[ℂ] RightQuark) →ₗ[ℂ] ColorPair :=
  (TensorProduct.rid ℂ ColorPair).toLinearMap.comp
    ((TensorProduct.map LinearMap.id weakTensor).comp
      (TensorProduct.tensorTensorTensorComm ℂ Color Spin Color Spin).toLinearMap)

@[simp] theorem diquark_tmul (a b : Color) (s t : Spin) :
    diquark ((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] t)) =
      eps2 s t • (a ⊗ₜ[ℂ] b) := by
  simp [diquark]

@[simp] theorem eps2Bilin_self (s : Spin) : eps2Bilin s s = 0 := by
  simp [eps2Bilin, eps2]
  ring

private def threeDiquarks : SixSlotAlternation.OrderedSpace RightQuark RightQuark →ₗ[ℂ]
    ((ColorPair ⊗[ℂ] ColorPair) ⊗[ℂ] ColorPair) :=
  TensorProduct.map (TensorProduct.map diquark diquark) diquark

/-- The all-right-handed ordered `O^3_RRR`-type contraction of Eq. (1) in
arXiv:1901.07519, before exterior alternatization and normalization choices. -/
def orderedContraction :
    SixSlotAlternation.OrderedSpace RightQuark RightQuark →ₗ[ℂ] ℂ :=
  colorAAS.comp threeDiquarks

@[simp] theorem orderedContraction_tmul
    (a b c d e f : Color) (s t u v w x : Spin) :
    orderedContraction (((((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ]
      ((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (d ⊗ₜ[ℂ] v))) ⊗ₜ[ℂ]
        ((e ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] (f ⊗ₜ[ℂ] x)))) =
      (eps3 a b e * eps3 c d f + eps3 a b f * eps3 c d e) *
        (eps2 s t * eps2 u v * eps2 w x) := by
  simp [orderedContraction, threeDiquarks, smul_eq_mul]
  simp [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  ring

abbrev SymmetryGroup := StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group

def upField : Representation ℂ SymmetryGroup RightQuark :=
  external StandardSMGaugeTensor.upRight WeylSpinor.right

def downField : Representation ℂ SymmetryGroup RightQuark :=
  external StandardSMGaugeTensor.downRight WeylSpinor.right

theorem rightEps_invariant (g : WeylSpinor.Group) (s t : Spin) :
    eps2 (WeylSpinor.right g s) (WeylSpinor.right g t) = eps2 s t := by
  rw [WeylSpinor.right_apply, WeylSpinor.right_apply]
  exact eps2_invariant _ (WeylSpinor.conjugate g).property s t

theorem sixQuark_phases (g : StandardSMGaugeTensor.GaugeGroup) :
    StandardSMGaugeTensor.phase 4 g * StandardSMGaugeTensor.phase (-2) g *
      StandardSMGaugeTensor.phase 4 g * StandardSMGaugeTensor.phase (-2) g *
      StandardSMGaugeTensor.phase (-2) g * StandardSMGaugeTensor.phase (-2) g = 1 := by
  have h : g.2.2 ^ (4 : ℤ) * g.2.2 ^ (-2 : ℤ) * g.2.2 ^ (4 : ℤ) *
      g.2.2 ^ (-2 : ℤ) * g.2.2 ^ (-2 : ℤ) * g.2.2 ^ (-2 : ℤ) = 1 := by group
  change (↑(g.2.2 ^ (4 : ℤ)) : ℂ) * ↑(g.2.2 ^ (-2 : ℤ)) *
    ↑(g.2.2 ^ (4 : ℤ)) * ↑(g.2.2 ^ (-2 : ℤ)) *
    ↑(g.2.2 ^ (-2 : ℤ)) * ↑(g.2.2 ^ (-2 : ℤ)) = 1
  simpa only [Circle.coe_mul, Circle.coe_one] using congrArg ((↑) : Circle → ℂ) h

theorem orderedContraction_invariant_linear (g : SymmetryGroup) :
    orderedContraction.comp (SixSlotAlternation.orderedRepresentation upField downField g) =
      orderedContraction := by
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro a
  apply LinearMap.ext; intro s
  apply TensorProduct.ext
  apply LinearMap.ext; intro b
  apply LinearMap.ext; intro t
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro c
  apply LinearMap.ext; intro u
  apply TensorProduct.ext
  apply LinearMap.ext; intro d
  apply LinearMap.ext; intro v
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro e
  apply LinearMap.ext; intro w
  apply TensorProduct.ext
  apply LinearMap.ext; intro f
  apply LinearMap.ext; intro x
  have hp : (StandardSMGaugeTensor.phase (-2) g.1) ^ 4 *
      (StandardSMGaugeTensor.phase 4 g.1) ^ 2 = 1 := by
    calc
      (StandardSMGaugeTensor.phase (-2) g.1) ^ 4 *
          (StandardSMGaugeTensor.phase 4 g.1) ^ 2 =
        StandardSMGaugeTensor.phase 4 g.1 * StandardSMGaugeTensor.phase (-2) g.1 *
          StandardSMGaugeTensor.phase 4 g.1 * StandardSMGaugeTensor.phase (-2) g.1 *
          StandardSMGaugeTensor.phase (-2) g.1 *
          StandardSMGaugeTensor.phase (-2) g.1 := by ring
      _ = 1 := sixQuark_phases g.1
  have hcolor :
      StandardSMGaugeTensor.phase (-2) g.1 *
          (StandardSMGaugeTensor.phase (-2) g.1 *
            (StandardSMGaugeTensor.phase 4 g.1 * eps3 a b e)) *
          (StandardSMGaugeTensor.phase (-2) g.1 *
            (StandardSMGaugeTensor.phase (-2) g.1 *
              (StandardSMGaugeTensor.phase 4 g.1 * eps3 c d f))) +
        StandardSMGaugeTensor.phase (-2) g.1 *
          (StandardSMGaugeTensor.phase (-2) g.1 *
            (StandardSMGaugeTensor.phase 4 g.1 * eps3 a b f)) *
          (StandardSMGaugeTensor.phase (-2) g.1 *
            (StandardSMGaugeTensor.phase (-2) g.1 *
              (StandardSMGaugeTensor.phase 4 g.1 * eps3 c d e))) =
        eps3 a b e * eps3 c d f + eps3 a b f * eps3 c d e := by
    calc
      _ = ((StandardSMGaugeTensor.phase (-2) g.1) ^ 4 *
          (StandardSMGaugeTensor.phase 4 g.1) ^ 2) *
          (eps3 a b e * eps3 c d f + eps3 a b f * eps3 c d e) := by ring
      _ = _ := by rw [hp]; ring
  simp [SixSlotAlternation.orderedRepresentation, upField, downField,
    external, StandardSMGaugeTensor.upRight, StandardSMGaugeTensor.downRight,
    StandardSMGaugeTensor.twist, Representation.tprod_apply,
    StandardSMGaugeTensor.color, Matrix.toLin'_apply,
    eps3_invariant _ g.1.1.prop.2, rightEps_invariant]
  exact Or.inl hcolor

def orderedIntertwiner : IntertwiningMap
    (SixSlotAlternation.orderedRepresentation upField downField)
    (Representation.trivial ℂ SymmetryGroup ℂ) where
  toLinearMap := orderedContraction
  isIntertwining' := orderedContraction_invariant_linear

def exteriorCoefficient : IntertwiningMap
    ((SixSlotAlternation.action upField downField).exteriorPower 6)
    (Representation.trivial ℂ SymmetryGroup ℂ) :=
  SixSlotAlternation.coefficient upField downField orderedIntertwiner

def rightBasis (c : Fin 3) (s : Fin 2) : RightQuark :=
  colorBasis c ⊗ₜ[ℂ] weakBasis s

def witness : Fin 6 → SixSlotAlternation.Fields RightQuark RightQuark :=
  SixSlotAlternation.slots
    (rightBasis 0 0) (rightBasis 0 1)
    (rightBasis 1 0) (rightBasis 1 1)
    (rightBasis 2 0) (rightBasis 2 1)

@[simp] theorem witness_zero : witness 0 = (rightBasis 0 0, 0) := rfl
@[simp] theorem witness_one : witness 1 = (0, rightBasis 1 0) := rfl
@[simp] theorem witness_two : witness 2 = (rightBasis 0 1, 0) := rfl
@[simp] theorem witness_three : witness 3 = (0, rightBasis 1 1) := rfl
@[simp] theorem witness_four : witness 4 = (0, rightBasis 2 0) := rfl
@[simp] theorem witness_five : witness 5 = (0, rightBasis 2 1) := rfl

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 1000000 in
theorem witness_evaluation :
    SixSlotAlternation.alternating orderedContraction witness = 24 := by
  classical
  unfold SixSlotAlternation.alternating
  rw [MultilinearMap.alternatization_apply]
  let spinIndex : Fin 6 → Fin 2 := ![0, 0, 1, 1, 0, 1]
  let good : Finset (Equiv.Perm (Fin 6)) := Finset.univ.filter fun s =>
    (s 0 = 0 ∨ s 0 = 2) ∧ (s 2 = 0 ∨ s 2 = 2) ∧
      spinIndex (s 0) ≠ spinIndex (s 1) ∧
      spinIndex (s 2) ≠ spinIndex (s 3) ∧
      spinIndex (s 4) ≠ spinIndex (s 5)
  let supportList : List (Equiv.Perm (Fin 6)) :=
    [Equiv.swap 1 3,
      Equiv.swap 1 3 * Equiv.swap 4 5,
      Equiv.swap 1 3 * Equiv.swap 3 4,
      Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 4 5,
      Equiv.swap 1 5 * Equiv.swap 3 5 * Equiv.swap 4 5,
      Equiv.swap 1 5 * Equiv.swap 3 5,
      Equiv.swap 1 5 * Equiv.swap 3 4 * Equiv.swap 4 5,
      Equiv.swap 1 5 * Equiv.swap 3 4,
      Equiv.swap 0 2,
      Equiv.swap 0 2 * Equiv.swap 4 5,
      Equiv.swap 0 2 * Equiv.swap 3 5 * Equiv.swap 4 5,
      Equiv.swap 0 2 * Equiv.swap 3 5,
      Equiv.swap 0 2 * Equiv.swap 1 4,
      Equiv.swap 0 2 * Equiv.swap 1 4 * Equiv.swap 4 5,
      Equiv.swap 0 2 * Equiv.swap 1 4 * Equiv.swap 3 5,
      Equiv.swap 0 2 * Equiv.swap 1 4 * Equiv.swap 3 5 * Equiv.swap 4 5]
  let support : Finset (Equiv.Perm (Fin 6)) := supportList.toFinset
  have hnodup : supportList.Nodup := by decide
  have hsupport : good = support := by decide
  have hsubset : good ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsubset (by
    intro s _ hs
    have hbad : ¬ ((s 0 = 0 ∨ s 0 = 2) ∧ (s 2 = 0 ∨ s 2 = 2) ∧
        spinIndex (s 0) ≠ spinIndex (s 1) ∧
        spinIndex (s 2) ≠ spinIndex (s 3) ∧
        spinIndex (s 4) ≠ spinIndex (s 5)) := by
      simpa [good] using hs
    by_cases h0 : s 0 = 0 ∨ s 0 = 2
    · by_cases h2 : s 2 = 0 ∨ s 2 = 2
      · have hspin : ¬ (spinIndex (s 0) ≠ spinIndex (s 1) ∧
            spinIndex (s 2) ≠ spinIndex (s 3) ∧
            spinIndex (s 4) ≠ spinIndex (s 5)) := fun h => hbad ⟨h0, h2, h⟩
        by_cases h01 : spinIndex (s 0) ≠ spinIndex (s 1)
        · by_cases h23 : spinIndex (s 2) ≠ spinIndex (s 3)
          · have h45 : spinIndex (s 4) = spinIndex (s 5) := by
              simpa [h01, h23] using hspin
            generalize hk4 : s 4 = k4
            generalize hk5 : s 5 = k5
            fin_cases k4 <;> fin_cases k5 <;>
              simp_all [spinIndex, SixSlotAlternation.ordered, witness,
                SixSlotAlternation.slots, rightBasis, orderedContraction,
                threeDiquarks, diquark, weakTensor, eps2Bilin, eps2, weakBasis,
                LinearEquiv.map_zero]
          · have heq : spinIndex (s 2) = spinIndex (s 3) := not_ne_iff.mp h23
            generalize hk2 : s 2 = k2
            generalize hk3 : s 3 = k3
            fin_cases k2 <;> fin_cases k3 <;>
              simp_all [spinIndex, SixSlotAlternation.ordered, witness,
                SixSlotAlternation.slots, rightBasis, orderedContraction,
                threeDiquarks, diquark, weakTensor, eps2Bilin, eps2, weakBasis,
                LinearEquiv.map_zero]
        · have heq : spinIndex (s 0) = spinIndex (s 1) := not_ne_iff.mp h01
          generalize hk0 : s 0 = k0
          generalize hk1 : s 1 = k1
          fin_cases k0 <;> fin_cases k1 <;>
            simp_all [spinIndex, SixSlotAlternation.ordered, witness,
              SixSlotAlternation.slots, rightBasis, orderedContraction,
              threeDiquarks, diquark, weakTensor, eps2Bilin, eps2, weakBasis,
              LinearEquiv.map_zero]
      · generalize hk : s 2 = k
        fin_cases k <;> simp_all [SixSlotAlternation.ordered, witness,
          SixSlotAlternation.slots]
    · generalize hk : s 0 = k
      fin_cases k <;> simp_all [SixSlotAlternation.ordered, witness,
        SixSlotAlternation.slots])]
  rw [hsupport]
  unfold support
  rw [List.sum_toFinset _ hnodup]
  norm_num
    [supportList, Equiv.swap_apply_def, Equiv.Perm.mul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      SixSlotAlternation.ordered,
      rightBasis, eps2, eps3, colorBasis, weakBasis, Pi.single_apply, Fin.ext_iff]

theorem exteriorCoefficient_witness :
    exteriorCoefficient (exteriorPower.ιMulti ℂ 6 witness) = 24 := by
  rw [exteriorCoefficient, SixSlotAlternation.coefficient_apply_ιMulti]
  exact witness_evaluation

theorem exteriorCoefficient_ne_zero : exteriorCoefficient ≠ 0 := by
  apply SixSlotAlternation.coefficient_ne_zero_of_evaluation
    upField downField orderedIntertwiner witness
  have h : SixSlotAlternation.alternating orderedIntertwiner.toLinearMap witness = 24 := by
    simpa [orderedIntertwiner] using witness_evaluation
  rw [h]
  norm_num

end
end GUT.DeltaBTwoSixQuark
