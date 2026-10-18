import Math.RepresentationTheory.InvariantCoefficientProduct
import Math.RepresentationTheory.InvariantPairing
import Math.RepresentationTheory.SU3DefiningExterior
import Math.RepresentationTheory.SU3DualExterior
import TauCeti.RepresentationTheory.Tensor.Power

/-! Uniform constructive positive scalar couplings of defining and dual
SU3 tensor powers. No numerical multiplicity or rank is evaluated. -/
namespace Math.SU3TensorPositive
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior InvariantCoefficientProduct ExternalInvariantTensor
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance

@[reducible] local instance (V : Type*) [AddCommGroup V] [Module ℂ V] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n V) := inferInstance

abbrev MixedCarrier (a b : ℕ) := (⨂[ℂ]^a Vector) ⊗[ℂ] (⨂[ℂ]^b (Module.Dual ℂ Vector))
@[reducible] local instance (a b : ℕ) : AddCommGroup (MixedCarrier a b) := inferInstance
abbrev mixed (a b : ℕ) : Representation ℂ Group (MixedCarrier a b) :=
  (rho.tensorPower a).tprod (rho.dual.tensorPower b)

def HasScalar (a b : ℕ) : Prop := HasUnit (mixed a b)

def zeroEquiv {V : Type*} [AddCommGroup V] [Module ℂ V] (r : Representation ℂ Group V) :
    Representation.Equiv (r.tensorPower 0) (trivial ℂ Group ℂ) where
  toLinearEquiv := PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℂ) (s := fun _ => V)
  isIntertwining' g := by
    rw [tensorPower_zero_apply]
    rfl

def oneEquiv {V : Type*} [AddCommGroup V] [Module ℂ V] (r : Representation ℂ Group V) :
    Representation.Equiv (r.tensorPower 1) r where
  toLinearEquiv := PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) 0
  isIntertwining' g := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp [Representation.tensorPower_apply,PiTensorProduct.map_tprod]

theorem zero : HasUnit (mixed 0 0) := by
  apply transport (tensorEquiv (zeroEquiv rho) (zeroEquiv rho.dual)).symm
  exact tensor ⟨IntertwiningMap.id _,1,rfl⟩ ⟨IntertwiningMap.id _,1,rfl⟩

abbrev evaluation := InvariantPairing.evaluation rho

theorem pair : HasUnit (mixed 1 1) := by
  apply transport (tensorEquiv (oneEquiv rho) (oneEquiv rho.dual)).symm
  exact ⟨evaluation,basis 0 ⊗ₜ[ℂ] (basis.coord 0),by simp [evaluation,basis]⟩

def determinantCoefficient {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ Group V) (b : Module.Basis (Fin 3) ℂ V)
    (hd : ∀ g, LinearMap.det (r g)=1) :
    InvariantCoefficientTransport.Invariants (r.tensorPower 3) where
  toLinearMap := PiTensorProduct.lift ((exteriorPower.topEquiv b).toLinearMap.compAlternatingMap
    (exteriorPower.ιMulti ℂ 3)).toMultilinearMap
  isIntertwining' g := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
      Representation.tensorPower_apply,PiTensorProduct.map_tprod,PiTensorProduct.lift.tprod]
    change exteriorPower.topEquiv b (exteriorPower.ιMulti ℂ 3 ((r g) ∘ v))=
      exteriorPower.topEquiv b (exteriorPower.ιMulti ℂ 3 v)
    rw [← exteriorPower.map_apply_ιMulti,exteriorPower.map_top_eq_det_smul b,hd g,one_smul]
    rfl

theorem determinant_unit {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ Group V) (b : Module.Basis (Fin 3) ℂ V)
    (hd : ∀ g, LinearMap.det (r g)=1) : HasUnit (r.tensorPower 3) :=
  ⟨determinantCoefficient r b hd,PiTensorProduct.tprod ℂ b,by
    simp only [determinantCoefficient,IntertwiningMap.coe_mk,PiTensorProduct.lift.tprod]
    change exteriorPower.topEquiv b (exteriorPower.ιMulti ℂ 3 b)=1
    rw [exteriorPower.topEquiv_apply_ιMulti,Module.Basis.det_self]⟩

theorem triple : HasUnit (mixed 3 0) := by
  have hz : HasUnit (rho.dual.tensorPower 0) :=
    transport (zeroEquiv rho.dual).symm ⟨IntertwiningMap.id _,1,rfl⟩
  exact tensor (determinant_unit rho basis determinant) hz

theorem dualTriple : HasUnit (mixed 0 3) := by
  apply transport (tensorEquiv (zeroEquiv rho) (.refl (rho.dual.tensorPower 3))).symm
  exact tensor ⟨IntertwiningMap.id _,1,rfl⟩
    (determinant_unit rho.dual SU3DualExterior.basis SU3DualExterior.determinant)

def regroup (a b c d : ℕ) : Representation.Equiv ((mixed a b).tprod (mixed c d))
    (mixed (a+c) (b+d)) :=
  (ExternalInvariantTensor.regroupPairDiagonal (rho.tensorPower a) (rho.tensorPower c)
    (rho.dual.tensorPower b) (rho.dual.tensorPower d)).trans
      (tensorEquiv (rho.tensorPowerAddEquiv a c) (rho.dual.tensorPowerAddEquiv b d))

theorem add {a b c d : ℕ} (h : HasUnit (mixed a b)) (k : HasUnit (mixed c d)) :
    HasUnit (mixed (a+c) (b+d)) := transport (regroup a b c d) (tensor h k)

theorem diagonal (n : ℕ) : HasUnit (mixed n n) := by
  induction n with
  | zero => exact zero
  | succ n ih => exact add ih pair

theorem triples (n : ℕ) : HasUnit (mixed (3*n) 0) := by
  induction n with
  | zero => simpa using zero
  | succ n ih => simpa only [Nat.mul_succ,Nat.zero_add] using add ih triple

theorem dualTriples (n : ℕ) : HasUnit (mixed 0 (3*n)) := by
  induction n with
  | zero => simpa using zero
  | succ n ih => simpa only [Nat.mul_succ,Nat.zero_add] using add ih dualTriple

/-- A uniform explicit positive criterion, proved by evaluation pairs and
color/dual-color determinant triples, independent of tensor degree. -/
theorem positive (a b : ℕ) (h : a%3=b%3) : HasUnit (mixed a b) := by
  have hp := add (add (triples (a/3)) (dualTriples (b/3))) (diagonal (a%3))
  have ha : 3*(a/3)+a%3=a := by omega
  have hb : 3*(b/3)+a%3=b := by omega
  change HasScalar _ _ at hp
  change HasScalar a b
  simpa only [Nat.add_zero,Nat.zero_add,ha,hb] using hp

end
end Math.SU3TensorPositive
