import Physics.StandardModel.Gauge.Tensors.SMEpsilonUniqueness
import Physics.StandardModel.Gauge.Tensors.StandardSMGaugeTensor
import Math.RepresentationTheory.Tensors.TwoComponentContractions
import Math.RepresentationTheory.Invariants.InvariantEvaluation
import Math.RepresentationTheory.Tensors.TwoComponentAdjoint
import Math.RepresentationTheory.Tensors.TwoComponentTripletDual

open Math

/-! Exhaustive weak singlet and triplet dipole contractions. The conjugate
Higgs is written as a pseudoreal weak doublet, with its original charge. -/
namespace Physics.DipoleGaugeTensor
set_option autoImplicit false
noncomputable section
open Representation TwoComponentSymmetricTensor TwoComponentTensorUniqueness
open TwoComponentContractions SMEpsilonTensor
open scoped TensorProduct

def weak : Representation ℂ WeakGroup Doublet := doublet.comp weakToSL
def adjoint : Representation ℂ WeakGroup Triplet := triplet.comp weakToSL
def singletRepresentation := weak.tprod weak
def tripletRepresentation := singletRepresentation.tprod adjoint.dual

def singlet : IntertwiningMap singletRepresentation
    (Representation.trivial ℂ WeakGroup ℂ) where
  toLinearMap := weakTensor
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    exact eps2_invariant _ g.prop.2 x y

def tripletContraction : IntertwiningMap tripletRepresentation
    (Representation.trivial ℂ WeakGroup ℂ) :=
  InvariantEvaluation.contraction singletRepresentation adjoint (restrictedPair weakToSL)

def singletWitness := basis2 0 ⊗ₜ[ℂ] basis2 1
def coordinate : Module.Dual ℂ Triplet := (Pi.basisFun ℂ (Fin 3)).coord 0
def tripletWitness := (basis2 0 ⊗ₜ[ℂ] basis2 0) ⊗ₜ[ℂ] coordinate

@[simp] theorem singlet_tmul (x y : Doublet) : singlet (x ⊗ₜ[ℂ] y) = eps2 x y := rfl
@[simp] theorem triplet_tmul (x y : Doublet) (F : Module.Dual ℂ Triplet) :
    tripletContraction ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] F) = F (pair (x ⊗ₜ[ℂ] y)) := rfl

@[simp] theorem singlet_normalized : singlet singletWitness = 1 := by
  norm_num [singletWitness, basis2, eps2]
@[simp] theorem triplet_normalized : tripletContraction tripletWitness = 1 := by
  simp [tripletWitness, coordinate, basis2, Module.Basis.coord_apply]

theorem singlet_unique (f : IntertwiningMap singletRepresentation
    (Representation.trivial ℂ WeakGroup ℂ)) : f = f singletWitness • singlet := by
  have h := SMEpsilonUniqueness.weak_unique (TensorProduct.curry f.toLinearMap)
    (fun g x y => IntertwiningMap.isIntertwining _ _ f g (x ⊗ₜ[ℂ] y))
  apply IntertwiningMap.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

theorem triplet_unique (f : IntertwiningMap tripletRepresentation
    (Representation.trivial ℂ WeakGroup ℂ)) :
    f = f tripletWitness • tripletContraction := by
  apply InvariantEvaluation.unique singletRepresentation adjoint (restrictedPair weakToSL)
    (basis2 0 ⊗ₜ[ℂ] basis2 0) coordinate
  · exact triplet_normalized
  · intro k
    exact ⟨value weakToSL k 0 0 0, TwoComponentContractions.weak_unique k⟩

def toDual : IntertwiningMap weak weak.dual := InvariantTensorCurry.curry weak weak singlet

def fromDual : Module.Dual ℂ Doublet →ₗ[ℂ] Doublet where
  toFun phi := ![phi (basis2 1), -phi (basis2 0)]
  map_add' phi psi := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' z phi := by ext i; fin_cases i <;> simp

/-- The actual weak-dual Higgs is identified by epsilon, not by a charge test. -/
def weakDualEquiv : Representation.Equiv weak weak.dual where
  toLinearEquiv := {
    toLinearMap := toDual.toLinearMap
    invFun := fromDual
    left_inv x := by
      ext i
      change ![eps2 x (basis2 1), -eps2 x (basis2 0)] i = x i
      fin_cases i <;> simp [eps2, basis2]
    right_inv phi := by
      apply (Pi.basisFun ℂ (Fin 2)).ext
      intro i
      simp only [Pi.basisFun_apply]
      change eps2 (fromDual phi) (Pi.single i 1) = phi (Pi.single i 1)
      fin_cases i <;> simp [fromDual, eps2, basis2] }
  isIntertwining' := toDual.isIntertwining'

/-- All-left conjugate dipole hypercharges, in the repository's 6Y units. -/
theorem phases (g : StandardSMGaugeTensor.GaugeGroup) :
    StandardSMGaugeTensor.phase (-3) g * StandardSMGaugeTensor.phase 6 g *
      StandardSMGaugeTensor.phase (-3) g = 1 := by
  have h : g.2.2 ^ (-3 : ℤ) * g.2.2 ^ (6 : ℤ) * g.2.2 ^ (-3 : ℤ) = 1 := by group
  change (↑(g.2.2 ^ (-3 : ℤ)) : ℂ) * ↑(g.2.2 ^ (6 : ℤ)) *
    ↑(g.2.2 ^ (-3 : ℤ)) = 1
  simpa only [Circle.coe_mul, Circle.coe_one] using congrArg ((↑) : Circle → ℂ) h

end
end Physics.DipoleGaugeTensor
