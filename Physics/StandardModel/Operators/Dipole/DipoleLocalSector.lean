import Physics.StandardModel.Gauge.Tensors.DipoleGaugeTensor
import Physics.FieldTheory.Spinor.Tensors.DipoleSpinorTensor
import Math.RepresentationTheory.Invariants.NormalizedInvariantFactor
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport

open Math

/-! Independent ordered local dipole sectors, before residual multiplicities.
L and Ec are distinct fermion slots; Higgs and field strength are bosonic. -/
namespace Physics.DipoleLocalSector
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open TwoComponentSymmetricTensor TwoComponentContractions
open scoped TensorProduct

local instance : AddCommGroup (Doublet ⊗[ℂ] Doublet) := inferInstance
local instance : AddCommGroup (Doublet ⊗[ℂ] Doublet ⊗[ℂ] Module.Dual ℂ Triplet) := inferInstance
local instance : AddCommGroup (WeylSpinor.Space ⊗[ℂ] WeylSpinor.Space ⊗[ℂ]
  DipoleSpinorTensor.Strength) := inferInstance

abbrev Group := WeakGroup × WeylSpinor.Group
def lepton := external DipoleGaugeTensor.weak WeylSpinor.left
def electron : Representation ℂ Group WeylSpinor.Space :=
  WeylSpinor.left.comp (MonoidHom.snd _ _)
def higgs : Representation ℂ Group Doublet :=
  DipoleGaugeTensor.weak.comp (MonoidHom.fst _ _)
def strengthB : Representation ℂ Group DipoleSpinorTensor.Strength :=
  DipoleSpinorTensor.strength.comp (MonoidHom.snd _ _)
def strengthW := external DipoleGaugeTensor.adjoint.dual DipoleSpinorTensor.strength

def orderedB := (lepton.tprod electron).tprod (higgs.tprod strengthB)
def orderedW := (lepton.tprod electron).tprod (higgs.tprod strengthW)
def factoredB := external DipoleGaugeTensor.singletRepresentation DipoleSpinorTensor.localRepresentation
def factoredW := external DipoleGaugeTensor.tripletRepresentation DipoleSpinorTensor.localRepresentation

def regroupB : Representation.Equiv orderedB factoredB where
  toLinearEquiv :=
    (TensorProduct.congr (TensorProduct.assoc ℂ Doublet WeylSpinor.Space WeylSpinor.Space)
      (LinearEquiv.refl ℂ _)).trans
      (TensorProduct.tensorTensorTensorComm ℂ Doublet
        (WeylSpinor.Space ⊗[ℂ] WeylSpinor.Space) Doublet DipoleSpinorTensor.Strength)
  isIntertwining' g := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro s
    apply LinearMap.ext; intro t
    apply TensorProduct.ext
    apply LinearMap.ext; intro h
    apply LinearMap.ext; intro F
    rfl

def regroupW : Representation.Equiv orderedW factoredW where
  toLinearEquiv :=
    (((TensorProduct.congr (TensorProduct.assoc ℂ Doublet WeylSpinor.Space WeylSpinor.Space)
      (LinearEquiv.refl ℂ _)).trans
      (TensorProduct.tensorTensorTensorComm ℂ Doublet
        (WeylSpinor.Space ⊗[ℂ] WeylSpinor.Space) Doublet
          (Module.Dual ℂ Triplet ⊗[ℂ] DipoleSpinorTensor.Strength))).trans
        (TensorProduct.assoc ℂ (Doublet ⊗[ℂ] Doublet)
          (WeylSpinor.Space ⊗[ℂ] WeylSpinor.Space)
          (Module.Dual ℂ Triplet ⊗[ℂ] DipoleSpinorTensor.Strength)).symm).trans
      (TensorProduct.tensorTensorTensorComm ℂ (Doublet ⊗[ℂ] Doublet)
        (WeylSpinor.Space ⊗[ℂ] WeylSpinor.Space)
        (Module.Dual ℂ Triplet) DipoleSpinorTensor.Strength)
  isIntertwining' g := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro s
    apply LinearMap.ext; intro t
    apply TensorProduct.ext
    apply LinearMap.ext; intro h
    apply TensorProduct.ext
    apply LinearMap.ext; intro W
    apply LinearMap.ext; intro F
    rfl

def contractionB := coefficient DipoleGaugeTensor.singlet DipoleSpinorTensor.contraction
def contractionW := coefficient DipoleGaugeTensor.tripletContraction DipoleSpinorTensor.contraction
def witnessB := DipoleGaugeTensor.singletWitness ⊗ₜ[ℂ] DipoleSpinorTensor.witness
def witnessW := DipoleGaugeTensor.tripletWitness ⊗ₜ[ℂ] DipoleSpinorTensor.witness

@[simp] theorem normalizedB : contractionB witnessB = 1 := by simp [contractionB, witnessB]
@[simp] theorem normalizedW : contractionW witnessW = 1 := by simp [contractionW, witnessW]

theorem uniqueB (f : InvariantCoefficientTransport.Invariants factoredB) :
    f = f witnessB • contractionB :=
  NormalizedInvariantFactor.product_unique DipoleGaugeTensor.singletRepresentation
    DipoleSpinorTensor.localRepresentation DipoleGaugeTensor.singlet DipoleSpinorTensor.contraction
    DipoleGaugeTensor.singletWitness DipoleSpinorTensor.witness
    DipoleGaugeTensor.singlet_unique DipoleSpinorTensor.unique f

theorem uniqueW (f : InvariantCoefficientTransport.Invariants factoredW) :
    f = f witnessW • contractionW :=
  NormalizedInvariantFactor.product_unique DipoleGaugeTensor.tripletRepresentation
    DipoleSpinorTensor.localRepresentation DipoleGaugeTensor.tripletContraction DipoleSpinorTensor.contraction
    DipoleGaugeTensor.tripletWitness DipoleSpinorTensor.witness
    DipoleGaugeTensor.triplet_unique DipoleSpinorTensor.unique f

end
end Physics.DipoleLocalSector
