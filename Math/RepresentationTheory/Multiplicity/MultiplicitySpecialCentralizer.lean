import Math.RepresentationTheory.Multiplicity.MultiplicityUnitaryCentralizer
import Math.RepresentationTheory.Multiplicity.HilbertMultiplicityDeterminant

/-!
# Special-unitary centralizers and the full weighted determinant kernel

The determinant constraint uses the actual dimensions of the simple
constituents. All solutions are retained, including finite components.
-/

namespace Math.MultiplicitySpecialCentralizer

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MonoidAlgebra Math.IsometricMultiplicity
open UnitaryCentralizerTransport

variable {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ G E) (D : MultiplicityCommutant.Model ℂ[G] rho.asModule)
  [Fintype (isotypicComponents ℂ[G] rho.asModule)]

local instance simpleInner : ∀ c, InnerProductSpace ℂ (D.simple c) :=
  IsometricMultiplicity.simpleInnerProductSpace rho D

local instance simpleFinite : ∀ c, FiniteDimensional ℂ (D.simple c) :=
  fun c => MultiplicityCommutant.Model.simple_finiteDimensional (k := ℂ) D c

local notation "tau" => IsometricMultiplicity.action rho D

/-- The determinant character with the actual constituent dimensions as exponents. -/
abbrev weightedDet := MultiplicityMatrix.weightedDet D.multiplicity
  (fun c => Module.finrank ℂ (D.simple c))

abbrev kernel := MultiplicityMatrix.specialMultiplicityGroup D.multiplicity
  (fun c => Module.finrank ℂ (D.simple c))

theorem determinant_unitaryMap (A : Π c, Matrix.unitaryGroup (Fin (D.multiplicity c)) ℂ) :
    determinant tau (MultiplicityUnitaryCentralizer.unitaryMap rho D A) = weightedDet rho D A := by
  classical
  exact HilbertMultiplicityOperator.det_operator D.multiplicity (fun c => D.simple c) (fun c => A c)

theorem determinant_modelUnitaryEquiv (h : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (A : Π c, Matrix.unitaryGroup (Fin (D.multiplicity c)) ℂ) :
    determinant tau (MultiplicityUnitaryCentralizer.modelUnitaryEquiv rho D h A) =
      weightedDet rho D A := determinant_unitaryMap rho D A

/-- Exactly the weighted determinant-one tuples give the Hilbert-model SU centralizer. -/
def modelSpecialEquiv (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    kernel rho D ≃ₜ* specialCentralizer tau := by
  let f := MultiplicityUnitaryCentralizer.modelUnitaryEquiv rho D h
  have hf (A : kernel rho D) : f A.1 ∈ specialCentralizer tau := by
    change determinant tau (f A.1) = 1
    exact (determinant_modelUnitaryEquiv rho D h A.1).trans A.2
  have hf' (u : specialCentralizer tau) : f.symm u.1 ∈ kernel rho D := by
    change weightedDet rho D (f.symm u.1) = 1
    exact (determinant_modelUnitaryEquiv rho D h (f.symm u.1)).symm.trans
      ((congrArg (determinant tau) (f.apply_symm_apply u.1)).trans u.2)
  exact
    { toFun := fun A => ⟨f A.1, hf A⟩
      invFun := fun u => ⟨f.symm u.1, hf' u⟩
      left_inv := fun A => Subtype.ext (f.left_inv A.1)
      right_inv := fun u => Subtype.ext (f.right_inv u.1)
      map_mul' := fun A B => Subtype.ext (f.map_mul A.1 B.1)
      continuous_toFun := (f.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (f.symm.continuous.comp continuous_subtype_val).subtype_mk _ }

/-- The actual SU centralizer, with no replacement by its identity component. -/
def specialCentralizerEquiv (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    specialCentralizer rho ≃ₜ* kernel rho D :=
  (IsometricMultiplicity.specialCentralizerEquiv rho D h).trans (modelSpecialEquiv rho D h).symm

end

end Math.MultiplicitySpecialCentralizer
