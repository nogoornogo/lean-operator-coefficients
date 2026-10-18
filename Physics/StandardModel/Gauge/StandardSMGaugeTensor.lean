import Physics.StandardModel.Gauge.SMEpsilonTensor
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Circle

/-!
# Actual Standard Model gauge tensors for qque and duql

The gauge group here is the covering product SU(3) x SU(2) x U(1),
with integral hypercharges 6Y. These are ordered internal gauge tensors;
Lorentz factors, Grassmann quotients, and mass-radical embeddings are not
part of this construction.
-/

set_option autoImplicit false

namespace GUT.StandardSMGaugeTensor

noncomputable section

open SMEpsilonTensor
open scoped TensorProduct

abbrev GaugeGroup := Matrix.specialUnitaryGroup (Fin 3) ℂ ×
  Matrix.specialUnitaryGroup (Fin 2) ℂ × Circle

def color : Representation ℂ GaugeGroup Color where
  toFun g := Matrix.toLin' (g.1 : Matrix (Fin 3) (Fin 3) ℂ)
  map_one' := Matrix.toLin'_one
  map_mul' _g _h := Matrix.toLin'_mul _ _

def weak : Representation ℂ GaugeGroup Weak where
  toFun g := Matrix.toLin' (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := Matrix.toLin'_one
  map_mul' _g _h := Matrix.toLin'_mul _ _

def phase (y : ℤ) : GaugeGroup →* ℂ :=
  Circle.coeHom.comp ((zpowGroupHom y).comp
    ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)))

def twist {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ GaugeGroup V) (y : ℤ) : Representation ℂ GaugeGroup V where
  toFun g := phase y g • rho g
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

abbrev Quark := Color ⊗[ℂ] Weak
def quark : Representation ℂ GaugeGroup Quark := twist (color.tprod weak) 1
def upRight : Representation ℂ GaugeGroup Color := twist color 4
def downRight : Representation ℂ GaugeGroup Color := twist color (-2)
def lepton : Representation ℂ GaugeGroup Weak := twist weak (-3)
def electronRight : Representation ℂ GaugeGroup ℂ :=
  twist (Representation.trivial ℂ GaugeGroup ℂ) (-6)

abbrev QQueSpace := (Quark ⊗[ℂ] Quark) ⊗[ℂ] (Color ⊗[ℂ] ℂ)
abbrev DuqlSpace := (Color ⊗[ℂ] Color) ⊗[ℂ] (Quark ⊗[ℂ] Weak)

def qqueRepresentation : Representation ℂ GaugeGroup QQueSpace :=
  (quark.tprod quark).tprod (upRight.tprod electronRight)

def duqlRepresentation : Representation ℂ GaugeGroup DuqlSpace :=
  (downRight.tprod upRight).tprod (quark.tprod lepton)

private def contract : ((Color ⊗[ℂ] Color) ⊗[ℂ] Color) ⊗[ℂ] (Weak ⊗[ℂ] Weak) →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp (TensorProduct.map colorTensor weakTensor)

def qque : QQueSpace →ₗ[ℂ] ℂ :=
  contract.comp ((TensorProduct.map LinearMap.id (TensorProduct.rid ℂ _).toLinearMap).comp
    ((TensorProduct.tensorTensorTensorComm ℂ _ _ _ _).toLinearMap.comp
      (TensorProduct.map (TensorProduct.tensorTensorTensorComm ℂ Color Weak Color Weak).toLinearMap
        LinearMap.id)))

def duql : DuqlSpace →ₗ[ℂ] ℂ :=
  contract.comp ((TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.comp
    (TensorProduct.map LinearMap.id (TensorProduct.assoc ℂ Color Weak Weak).toLinearMap))

@[simp] theorem qque_tmul (a b c : Color) (x y : Weak) (e : ℂ) :
    qque (((a ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] e)) =
      eps3 a b c * eps2 x y * e := by
  simp [qque, contract, mul_comm]

@[simp] theorem duql_tmul (a b c : Color) (x y : Weak) :
    duql ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] ((c ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y)) =
      eps3 a b c * eps2 x y := by
  simp [duql, contract]

theorem qque_phases (g : GaugeGroup) :
    phase 1 g * phase 1 g * phase 4 g * phase (-6) g = 1 := by
  have h : g.2.2 ^ (1 : ℤ) * g.2.2 ^ (1 : ℤ) * g.2.2 ^ (4 : ℤ) *
      g.2.2 ^ (-6 : ℤ) = 1 := by group
  change (↑(g.2.2 ^ (1 : ℤ)) : ℂ) * ↑(g.2.2 ^ (1 : ℤ)) *
    ↑(g.2.2 ^ (4 : ℤ)) * ↑(g.2.2 ^ (-6 : ℤ)) = 1
  simpa only [Circle.coe_mul, Circle.coe_one] using congrArg ((↑) : Circle → ℂ) h

theorem duql_phases (g : GaugeGroup) :
    phase (-2) g * phase 4 g * phase 1 g * phase (-3) g = 1 := by
  have h : g.2.2 ^ (-2 : ℤ) * g.2.2 ^ (4 : ℤ) * g.2.2 ^ (1 : ℤ) *
      g.2.2 ^ (-3 : ℤ) = 1 := by group
  change (↑(g.2.2 ^ (-2 : ℤ)) : ℂ) * ↑(g.2.2 ^ (4 : ℤ)) *
    ↑(g.2.2 ^ (1 : ℤ)) * ↑(g.2.2 ^ (-3 : ℤ)) = 1
  simpa only [Circle.coe_mul, Circle.coe_one] using congrArg ((↑) : Circle → ℂ) h

theorem qque_invariant_linear (g : GaugeGroup) :
    qque.comp (qqueRepresentation g) = qque := by
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro a
  apply LinearMap.ext; intro x
  apply TensorProduct.ext
  apply LinearMap.ext; intro b
  apply LinearMap.ext; intro y
  apply TensorProduct.ext
  apply LinearMap.ext; intro c
  apply LinearMap.ext; intro e
  simp [qqueRepresentation, quark, upRight, electronRight, twist,
    Representation.tprod_apply, TensorProduct.smul_tmul',
    color, weak, Matrix.toLin'_apply,
    eps3_invariant _ g.1.prop.2, eps2_invariant _ g.2.1.prop.2]
  linear_combination (eps3 a b c * eps2 x y * e) * qque_phases g

theorem duql_invariant_linear (g : GaugeGroup) :
    duql.comp (duqlRepresentation g) = duql := by
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro a
  apply LinearMap.ext; intro b
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro c
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  simp [duqlRepresentation, downRight, upRight, quark, lepton, twist,
    Representation.tprod_apply, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    color, weak, Matrix.toLin'_apply,
    eps3_invariant _ g.1.prop.2, eps2_invariant _ g.2.1.prop.2]
  left
  linear_combination eps3 a b c * duql_phases g

def qqueIntertwiner : Representation.IntertwiningMap qqueRepresentation
    (Representation.trivial ℂ GaugeGroup ℂ) where
  toLinearMap := qque
  isIntertwining' g := qque_invariant_linear g

def duqlIntertwiner : Representation.IntertwiningMap duqlRepresentation
    (Representation.trivial ℂ GaugeGroup ℂ) where
  toLinearMap := duql
  isIntertwining' g := duql_invariant_linear g

def qqueWitness : QQueSpace :=
  ((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] (colorBasis 1 ⊗ₜ[ℂ] weakBasis 1)) ⊗ₜ[ℂ]
    (colorBasis 2 ⊗ₜ[ℂ] (1 : ℂ))

def duqlWitness : DuqlSpace :=
  (colorBasis 0 ⊗ₜ[ℂ] colorBasis 1) ⊗ₜ[ℂ]
    ((colorBasis 2 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] weakBasis 1)

@[simp] theorem qque_witness : qque qqueWitness = 1 := by simp [qqueWitness]
@[simp] theorem duql_witness : duql duqlWitness = 1 := by simp [duqlWitness]

theorem qque_nonzero : qque ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun h qqueWitness
  simp at he

theorem duql_nonzero : duql ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun h duqlWitness
  simp at he

end

end GUT.StandardSMGaugeTensor
