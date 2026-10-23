import Math.RepresentationTheory.Coefficients.SelfDualCoefficient

/-! A distinct module carrier fixes the algebraic presentation before
specializing a representation. Coefficients return to the actual source
through a proved representation equivalence. -/
namespace Math.CarrierPresentation
set_option autoImplicit false
noncomputable section
open Representation


variable {G U V : Type*} [Group G] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup V] [Module ℂ V]

/-- Conjugate along a fixed linear presentation before taking any powers. -/
def actionAlong (E : U ≃ₗ[ℂ] V) (r : Representation ℂ G V) : Representation ℂ G U where
  toFun g := (E.symm.toLinearMap.comp (r g)).comp E.toLinearMap
  map_one' := by ext x; exact E.injective (by simp)
  map_mul' g h := by ext x; exact E.injective (by simp [Module.End.mul_apply])

def equivAlong (E : U ≃ₗ[ℂ] V) (r : Representation ℂ G V) :
    Representation.Equiv (actionAlong E r) r where
  toLinearEquiv := E
  isIntertwining' g := by ext x; exact E.apply_symm_apply _

theorem actionAlong_det (E : U ≃ₗ[ℂ] V) (r : Representation ℂ G V) (g : G) :
    LinearMap.det (actionAlong E r g) = LinearMap.det (r g) := by
  change LinearMap.det ((E.symm.toLinearMap.comp (r g)).comp E.toLinearMap) = _
  exact LinearMap.det_conj (r g) E.symm


structure Carrier (V : Type*) where
  val : V

namespace Carrier
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

def equiv : Carrier V ≃ V where
  toFun := val
  invFun := mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

instance : AddCommGroup (Carrier V) := (equiv V).addCommGroup

def addEquiv : Carrier V ≃+ V := Equiv.addEquiv (equiv V)

instance : Module ℂ (Carrier V) := (addEquiv V).module ℂ

def linearEquiv : Carrier V ≃ₗ[ℂ] V := (addEquiv V).linearEquiv ℂ

instance [Nontrivial V] : Nontrivial (Carrier V) := (equiv V).nontrivial

variable {G : Type*} [Group G]

def action (r : Representation ℂ G V) : Representation ℂ G (Carrier V) where
  toFun g := ((linearEquiv V).symm.toLinearMap.comp (r g)).comp
    (linearEquiv V).toLinearMap
  map_one' := by
    ext x
    exact (linearEquiv V).injective (by simp)
  map_mul' g h := by
    ext x
    exact (linearEquiv V).injective (by simp [Module.End.mul_apply])

def representationEquiv (r : Representation ℂ G V) :
    Representation.Equiv (action V r) r where
  toLinearEquiv := linearEquiv V
  isIntertwining' g := by
    ext x
    exact (linearEquiv V).apply_symm_apply _

end Carrier

variable {G A B : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ G A) (b : Representation ℂ G B)

def selfDuality (e : Representation.Equiv a a.dual) :
    Representation.Equiv (Carrier.action A a) (Carrier.action A a).dual :=
  ((Carrier.representationEquiv A a).trans e).trans
    (SplitRepresentationProjection.dualEquiv (Carrier.representationEquiv A a)).symm

def injection (f : IntertwiningMap b a) :
    IntertwiningMap (Carrier.action B b) (Carrier.action A a) :=
  (Carrier.representationEquiv A a).symm.toIntertwiningMap.comp
    (f.comp (Carrier.representationEquiv B b).toIntertwiningMap)

theorem injection_injective (f : IntertwiningMap b a) (hf : Function.Injective f) :
    Function.Injective (injection a b f) :=
  (Carrier.representationEquiv A a).symm.injective.comp
    (hf.comp (Carrier.representationEquiv B b).injective)

def coefficientEquiv :
    InvariantCoefficientTransport.Invariants ((Carrier.action A a).tprod (Carrier.action B b)) ≃ₗ[ℂ]
      InvariantCoefficientTransport.Invariants (a.tprod b) :=
  InvariantCoefficientTransport.alongEquiv
    (ExternalInvariantTensor.tensorEquiv
      (Carrier.representationEquiv A a) (Carrier.representationEquiv B b))

/-- Construct on the distinct carriers and return to the original source. -/
theorem allowed [Nontrivial B] (e : Representation.Equiv a a.dual)
    (f : IntertwiningMap b a) (hf : Function.Injective f) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (a.tprod b)) :=
  (SelectionCriteria.allowed_equiv (coefficientEquiv a b)).mp
    (SelfDualCoefficient.allowed _ _ (selfDuality a e)
      (injection a b f) (injection_injective a b f hf))

end
end Math.CarrierPresentation
