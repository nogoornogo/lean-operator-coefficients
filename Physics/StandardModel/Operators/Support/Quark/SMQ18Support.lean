import TauCeti.LinearAlgebra.ExteriorPower.Basis
import Physics.StandardModel.Operators.Support.Decomposition.SMGenerationSupport
import Physics.StandardModel.Operators.Support.Coordinates.SMConstantWeakCapacity
import Math.RepresentationTheory.Coefficients.SelfDualCoefficient

/-! Structural Q18 support from the perfect middle exterior pairing.
No character recurrence, numerical multiplicity or rank certificate is used. -/
namespace Physics.SMQ18Support
set_option autoImplicit false
noncomputable section
open Math Representation SMGenerationCauchy
open scoped TensorProduct

attribute [local irreducible] TopExteriorCauchy.map SymmetricCauchy.map
  SU2SymmetricEmbeddings.omegaPower

abbrev Field := ((SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ]
  WeakDoubletScalars.Doublet) ⊗[ℂ] (Fin 3 → ℂ)

@[reducible] local instance : AddCommGroup
    (SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ]
      WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup Field := inferInstance

abbrev rho : Representation ℂ Group Field := generations SMGenerationCauchy.quark

theorem field_dimension : Module.finrank ℂ Field = 36 := by
  simp [Field, SMEpsilonTensor.Color, WeakDoubletScalars.Doublet,
    Module.finrank_tensorProduct]

theorem weak_det (g : Group) : LinearMap.det (weak g) = 1 := by
  change LinearMap.det (Matrix.toLin' (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1
  rw [LinearMap.det_toLin']
  exact g.2.1.prop.2

theorem field_det (g : Group) : LinearMap.det (rho g) = 1 := by
  have hq : LinearMap.det (quark g) = 1 :=
    TensorDeterminant.map_one (colorBasis.tensorProduct spinBasis) spinBasis
      ((color.tprod weak) g) (spin g)
      (TensorDeterminant.map_one colorBasis spinBasis (color g) (weak g)
        (color_det g) (weak_det g)) (spin_det g)
  exact TensorDeterminant.map_one
    ((colorBasis.tensorProduct spinBasis).tensorProduct spinBasis)
    (Pi.basisFun ℂ (Fin 3)) (quark g) (LinearMap.id) hq (by simp)

def middleDuality : Representation.Equiv (rho.exteriorPower 18)
    (rho.exteriorPower 18).dual :=
  ComplementaryExteriorDuality.equiv rho field_det
    (Module.Basis.exteriorPowerTopEquiv (Module.finBasis ℂ Field)) (by rw [field_dimension])



/-- Fix the species-zero module dictionary before passing to exterior powers. -/
def actualFieldEquiv :
    DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) 0 ≃ₗ[ℂ] Field where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def actualQuarkEquiv : Representation.Equiv
    ((SMCombinedCompactAction.field 0).comp inclusion) rho where
  toLinearEquiv := actualFieldEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (DFunLike.congr_fun actual_quark g) x

/-- A distinct generator carrier gives every later construction one module presentation. -/
structure PresentedField where
  val : Field

namespace PresentedField

def equiv : PresentedField ≃ Field where
  toFun := val
  invFun := mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

instance : AddCommGroup PresentedField := equiv.addCommGroup

def addEquiv : PresentedField ≃+ Field := Equiv.addEquiv equiv

instance : Module ℂ PresentedField := addEquiv.module ℂ

def linearEquiv : PresentedField ≃ₗ[ℂ] Field := addEquiv.linearEquiv ℂ

instance : FiniteDimensional ℂ PresentedField := linearEquiv.symm.finiteDimensional

def action : Representation ℂ Group PresentedField :=
  CarrierPresentation.actionAlong linearEquiv rho

def representationEquiv : Representation.Equiv action rho :=
  CarrierPresentation.equivAlong linearEquiv rho

theorem dimension : Module.finrank ℂ PresentedField = 36 :=
  linearEquiv.finrank_eq.trans field_dimension

theorem determinant (g : Group) : LinearMap.det (action g) = 1 :=
  (CarrierPresentation.actionAlong_det linearEquiv rho g).trans (field_det g)

def middleDuality : Representation.Equiv (action.exteriorPower 18)
    (action.exteriorPower 18).dual :=
  ComplementaryExteriorDuality.equiv action determinant
    (Module.Basis.exteriorPowerTopEquiv (Module.finBasis ℂ PresentedField)) (by rw [dimension])

end PresentedField

theorem semisimple_allowed (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 18) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((rho.exteriorPower 18).tprod (weak.symmetricPower m))) := by
  let : Nontrivial (Sym[ℂ]^m WeakDoubletScalars.Doublet) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      change 0 < Module.finrank ℂ (Sym[ℂ]^m (Fin 2 → ℂ))
      rw [TauCeti.SU2.finrank_symPower]
      omega)
  exact SMGenerationSupport.generation_triple_presented_coefficient
    quark rho PresentedField.action 6 18 m quarkSix quarkSix_injective (by decide)
    PresentedField.representationEquiv.symm PresentedField.representationEquiv.symm
    PresentedField.middleDuality (by decide) hm hmax

end
end Physics.SMQ18Support
