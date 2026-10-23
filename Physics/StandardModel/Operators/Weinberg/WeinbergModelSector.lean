import Physics.StandardModel.Operators.Weinberg.WeinbergResidualHom
import Physics.StandardModel.Operators.Weinberg.WeinbergPermutationCompleteness
import Math.RepresentationTheory.Exterior.ExteriorSquareTensorDescent
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport

open Math

/-! Independent exterior/symmetric sector in physical field order for the
weak, Lorentz and residual group. The SM hypercharge adapter is separate. -/
namespace Physics.WeinbergModelSector
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SMEpsilonTensor
open scoped TensorProduct
variable {R F : Type*} [Group R] [AddCommGroup F] [Module ℂ F]
  (a : Representation ℂ R F)

abbrev ReducedGroup (R : Type*) := (TwoComponentContractions.WeakGroup × WeylSpinor.Group) × R
abbrev Lepton (F : Type*) [AddCommGroup F] [Module ℂ F] :=
  (Weak ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] F

@[reducible] local instance : AddCommGroup (Weak ⊗[ℂ] WeylSpinor.Space) := inferInstance
@[reducible] local instance : AddCommGroup (Lepton F) := inferInstance
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^2 (Lepton F)) ⊗[ℂ] Sym[ℂ]^2 Weak) := inferInstance

def lepton : Representation ℂ (ReducedGroup R) (Lepton F) :=
  external (external DipoleGaugeTensor.weak WeylSpinor.left) a

def higgs : Representation ℂ (ReducedGroup R) Weak :=
  DipoleGaugeTensor.weak.comp ((MonoidHom.fst _ _).comp (MonoidHom.fst _ R))

abbrev ModelSector := IntertwiningMap
  (((lepton a).exteriorPower 2).tprod ((higgs (R := R)).symmetricPower 2))
  (Representation.trivial ℂ (ReducedGroup R) ℂ)

def regroup : (((Lepton F ⊗[ℂ] Lepton F) ⊗[ℂ] Sym[ℂ]^2 Weak)) ≃ₗ[ℂ]
    (((Weak ⊗[ℂ] Weak) ⊗[ℂ] Sym[ℂ]^2 Weak) ⊗[ℂ]
      (WeylSpinor.Space ⊗[ℂ] WeylSpinor.Space)) ⊗[ℂ] (F ⊗[ℂ] F) :=
  (TensorProduct.congr
    ((TensorProduct.tensorTensorTensorComm ℂ (Weak ⊗[ℂ] WeylSpinor.Space) F
      (Weak ⊗[ℂ] WeylSpinor.Space) F).trans
      (TensorProduct.congr (TensorProduct.tensorTensorTensorComm ℂ Weak WeylSpinor.Space
        Weak WeylSpinor.Space) (LinearEquiv.refl ℂ _))) (LinearEquiv.refl ℂ _)).trans
    ((TensorProduct.rightComm ℂ _ _ _).trans
      (TensorProduct.congr (TensorProduct.rightComm ℂ _ _ _) (LinearEquiv.refl ℂ _)))

@[simp] theorem regroup_apply (x y : Weak) (s t : WeylSpinor.Space)
    (u v : F) (h : Sym[ℂ]^2 Weak) :
    regroup ((((x ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] ((y ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] v)) ⊗ₜ[ℂ] h) =
      (((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] (s ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] v) := rfl

def regroupEquiv : Representation.Equiv
    (((lepton a).tprod (lepton a)).tprod ((higgs (R := R)).symmetricPower 2))
    (external WeinbergResidualHom.localRepresentation (a.tprod a)) where
  toLinearEquiv := regroup
  isIntertwining' g := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro s
    apply LinearMap.ext; intro u
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro y
    apply LinearMap.ext; intro t
    apply LinearMap.ext; intro v
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin 2) Weak)
    rintro _ ⟨h, rfl⟩
    rfl

abbrev TensorSector := ExteriorSquareTensorDescent.tensorIntertwiners
  (lepton a) ((higgs (R := R)).symmetricPower 2) (Representation.trivial ℂ (ReducedGroup R) ℂ)

def orderedEquiv := InvariantCoefficientTransport.alongEquiv (regroupEquiv a)

theorem orderedEquiv_apply (f : InvariantCoefficientTransport.Invariants
    (((lepton a).tprod (lepton a)).tprod ((higgs (R := R)).symmetricPower 2)))
    (x y : Weak) (s t : WeylSpinor.Space) (u v : F) (h : Fin 2 → Weak) :
    orderedEquiv a f (WeinbergResidualHom.input x y h s t u v) =
      f ((((x ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] ((y ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] v)) ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ h) := by
  exact congrArg f ((regroupEquiv a).toLinearEquiv.symm_apply_apply
    ((((x ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] ((y ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] v)) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ h))

def statisticsEquiv : TensorSector a ≃ₗ[ℂ] WeinbergResidualHom.sector a where
  toFun f := ⟨orderedEquiv a f.val, by
    intro x y h s t u v
    rw [orderedEquiv_apply, orderedEquiv_apply]
    exact f.property _ _ _⟩
  invFun f := ⟨(orderedEquiv a).symm f.val, by
    let k := (orderedEquiv a).symm f.val
    let b := TensorProduct.curry (TensorProduct.curry k.toLinearMap)
    have hs : b.flip = -b := by
      apply TensorProduct.ext
      apply TensorProduct.ext
      apply LinearMap.ext; intro x
      apply LinearMap.ext; intro s
      apply LinearMap.ext; intro u
      apply TensorProduct.ext
      apply TensorProduct.ext
      apply LinearMap.ext; intro y
      apply LinearMap.ext; intro t
      apply LinearMap.ext; intro v
      apply SymmetricSquareDescent.ext
      intro h
      change f.val (WeinbergResidualHom.input y x h t s v u) =
        -f.val (WeinbergResidualHom.input x y h s t u v)
      exact f.property x y h s t u v
    intro x y h
    exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun hs x) y) h⟩
  left_inv f := by apply Subtype.ext; exact (orderedEquiv a).symm_apply_apply f.val
  right_inv f := by apply Subtype.ext; exact (orderedEquiv a).apply_symm_apply f.val
  map_add' f g := by apply Subtype.ext; exact (orderedEquiv a).map_add f.val g.val
  map_smul' z f := by apply Subtype.ext; exact (orderedEquiv a).map_smul z f.val

/-- Classify the independent mixed exterior/symmetric domain, not an assembly image. -/
def sectorEquiv : ModelSector a ≃ₗ[ℂ] WeinbergResidualHom.sector a :=
  (ExteriorSquareTensorDescent.equivariantEquiv (lepton a)
    ((higgs (R := R)).symmetricPower 2) (Representation.trivial ℂ (ReducedGroup R) ℂ)).symm.trans
    (statisticsEquiv a)

def homEquiv : ModelSector a ≃ₗ[ℂ]
    IntertwiningMap (a.symmetricPower 2) (Representation.trivial ℂ R ℂ) :=
  (sectorEquiv a).trans (WeinbergPermutationCompleteness.homEquiv a)

/-- The shared statistics theorem changes neither the physical extraction nor
its inverse. No new condition is imposed on the mixed input domain. -/
theorem homEquiv_agrees : homEquiv a =
    (sectorEquiv a).trans (WeinbergResidualHom.homEquiv a) := by
  rw [homEquiv, WeinbergPermutationCompleteness.homEquiv_agrees]

theorem inverse_agrees : (homEquiv a).symm =
    ((sectorEquiv a).trans (WeinbergResidualHom.homEquiv a)).symm := by
  rw [homEquiv_agrees]

theorem sectorEquiv_apply (f : ModelSector a) (x y : Weak) (s t : WeylSpinor.Space)
    (u v : F) (h : Fin 2 → Weak) :
    (sectorEquiv a f).val (WeinbergResidualHom.input x y h s t u v) =
      f (exteriorPower.ιMulti ℂ 2 ![(x ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] u, (y ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] v] ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ h) := by
  change orderedEquiv a
    (ExteriorSquareTensorDescent.restrict _ _ _ f).val
    (WeinbergResidualHom.input x y h s t u v) = _
  rw [orderedEquiv_apply]
  rfl

end
end Physics.WeinbergModelSector
