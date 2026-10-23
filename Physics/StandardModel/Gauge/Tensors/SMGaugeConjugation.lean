import Math.RepresentationTheory.Unitary.SpecialUnitaryContragredient
import Physics.StandardModel.Gauge.Charges.HyperchargeTensorTransport
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection
import Mathlib.LinearAlgebra.Contraction

open Math

/-! Explicit charge-conjugating group transport of the finite SM gauge
carriers. No conjugation of residual multiplicity modules is assumed. -/
namespace Physics.SMGaugeConjugation
set_option autoImplicit false
noncomputable section
open Representation StandardSMGaugeTensor ExternalInvariantTensor

def conjugate : GaugeGroup →* GaugeGroup where
  toFun g := (SpecialUnitaryContragredient.conjugate 3 g.1,
    SpecialUnitaryContragredient.conjugate 2 g.2.1, g.2.2⁻¹)
  map_one' := by simp
  map_mul' g h := by simp [mul_comm]

theorem conjugate_involutive : Function.Involutive conjugate := by
  rintro ⟨a,b,z⟩
  change (SpecialUnitaryContragredient.conjugate 3 (SpecialUnitaryContragredient.conjugate 3 a),
    SpecialUnitaryContragredient.conjugate 2 (SpecialUnitaryContragredient.conjugate 2 b),
    (z⁻¹)⁻¹) = (a,b,z)
  rw [SpecialUnitaryContragredient.conjugate_involutive,
    SpecialUnitaryContragredient.conjugate_involutive, inv_inv]

theorem conjugate_surjective : Function.Surjective conjugate := conjugate_involutive.surjective

theorem phase_conjugate (y : ℤ) (g : GaugeGroup) : phase y (conjugate g) = phase (-y) g := by
  change ((g.2.2⁻¹ : Circle) : ℂ) ^ y = (g.2.2 : ℂ) ^ (-y)
  simp

def colorDual : Representation.Equiv color.dual (color.comp conjugate) where
  toLinearEquiv := SpecialUnitaryContragredient.coordinates 3
  isIntertwining' g := by
    ext f i
    exact congrArg (fun v : Fin 3 → ℂ => v i) (LinearMap.congr_fun
      ((SpecialUnitaryContragredient.dualEquiv 3).isIntertwining' g.1) f)

def weakDual : Representation.Equiv weak.dual (weak.comp conjugate) where
  toLinearEquiv := SpecialUnitaryContragredient.coordinates 2
  isIntertwining' g := by
    ext f i
    exact congrArg (fun v : Fin 2 → ℂ => v i) (LinearMap.congr_fun
      ((SpecialUnitaryContragredient.dualEquiv 2).isIntertwining' g.2.1) f)

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
  [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]

def tensorDual (a : Representation ℂ GaugeGroup A) (b : Representation ℂ GaugeGroup B) :
    Representation.Equiv (a.dual.tprod b.dual) (a.tprod b).dual where
  toLinearEquiv := TensorProduct.dualDistribEquiv ℂ A B
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro phi psi
    apply TensorProduct.ext'
    intro x y
    simp [Representation.tprod_apply, Representation.dual_apply, Module.Dual.transpose_apply]

def tensorConjugate (a : Representation ℂ GaugeGroup A) (b : Representation ℂ GaugeGroup B)
    (e : Representation.Equiv a.dual (a.comp conjugate))
    (f : Representation.Equiv b.dual (b.comp conjugate)) :
    Representation.Equiv (a.tprod b).dual ((a.tprod b).comp conjugate) where
  toLinearEquiv := ((tensorDual a b).symm.trans
    (tensorEquiv (a := a.dual) (b := a.comp conjugate)
      (c := b.dual) (d := b.comp conjugate) e f)).toLinearEquiv
  isIntertwining' g := by
    exact ((tensorDual a b).symm.trans
      (tensorEquiv (a := a.dual) (b := a.comp conjugate)
        (c := b.dual) (d := b.comp conjugate) e f)).isIntertwining' g

omit [FiniteDimensional ℂ A] [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B] in
def chargedDual (a : Representation ℂ GaugeGroup A)
    (e : Representation.Equiv a.dual (a.comp conjugate)) (y : ℤ) :
    Representation.Equiv (twist a y).dual ((twist a y).comp conjugate) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' g := by
    ext f
    change e ((twist a y).dual g f) = twist a y (conjugate g) (e f)
    have h : (twist a y).dual g f = phase (-y) g • a.dual g f := by
      ext v
      change f (phase y g⁻¹ • a g⁻¹ v) = phase (-y) g * f (a g⁻¹ v)
      rw [map_smul, HyperchargeTensorTransport.phase_inv, smul_eq_mul]
    rw [h, map_smul]
    change phase (-y) g • e (a.dual g f) = phase y (conjugate g) • a (conjugate g) (e f)
    rw [phase_conjugate]
    exact congrArg (fun v => phase (-y) g • v)
      (LinearMap.congr_fun (e.isIntertwining' g) f)

def quarkDual : Representation.Equiv quark.dual (quark.comp conjugate) :=
  chargedDual (A := Quark) (color.tprod weak)
    (tensorConjugate color weak colorDual weakDual) 1

def upDual : Representation.Equiv upRight.dual (upRight.comp conjugate) :=
  chargedDual color colorDual 4

def downDual : Representation.Equiv downRight.dual (downRight.comp conjugate) :=
  chargedDual color colorDual (-2)

def leptonDual : Representation.Equiv StandardSMGaugeTensor.lepton.dual
    (StandardSMGaugeTensor.lepton.comp conjugate) := chargedDual weak weakDual (-3)

noncomputable def lineDual : Representation.Equiv (Representation.trivial ℂ GaugeGroup ℂ).dual
    ((Representation.trivial ℂ GaugeGroup ℂ).comp conjugate) where
  toLinearEquiv := LinearMap.ringLmapEquivSelf ℂ ℂ ℂ
  isIntertwining' _ := by ext f; rfl

def electronDual : Representation.Equiv electronRight.dual (electronRight.comp conjugate) :=
  chargedDual (Representation.trivial ℂ GaugeGroup ℂ) lineDual (-6)

def higgsDual : Representation.Equiv (twist weak 3).dual ((twist weak 3).comp conjugate) :=
  chargedDual weak weakDual 3

/-- Involutive group transport also gives the opposite direction of the
finite gauge-carrier identification, without any bidual flavor assumption. -/
def unconjugate {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (a : Representation ℂ GaugeGroup V)
    (e : Representation.Equiv a.dual (a.comp conjugate)) :
    Representation.Equiv a (a.dual.comp conjugate) where
  toLinearEquiv := e.symm.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change e.symm (a g v) = a.dual (conjugate g) (e.symm v)
    apply e.injective
    change e (e.symm (a g v)) = e (a.dual (conjugate g) (e.symm v))
    rw [Representation.Equiv.apply_symm_apply]
    have h := LinearMap.congr_fun (e.isIntertwining' (conjugate g)) (e.symm v)
    change e (a.dual (conjugate g) (e.symm v)) =
      a (conjugate (conjugate g)) (e (e.symm v)) at h
    rw [conjugate_involutive, Representation.Equiv.apply_symm_apply] at h
    exact h.symm

end
end Physics.SMGaugeConjugation
