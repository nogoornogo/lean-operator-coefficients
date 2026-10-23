import TauCeti.LinearAlgebra.ExteriorPower.Basis
import Math.RepresentationTheory.Color.Diagrams.ColorWeakQuartic
import Math.RepresentationTheory.Color.SU3.SU3MiddleColor
import Math.RepresentationTheory.SU2.SU2ExteriorSliceModels
import Math.RepresentationTheory.SU2.SU2DoubletDuality

/-! Actual color/weak gauge factors and their complete exterior branches,
for the middle-degree Q spin-slice construction. -/
namespace Math.ColorWeakMiddleGauge
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open scoped TensorProduct
abbrev Group := SU3DefiningExterior.Group × WeakDoubletScalars.Group
abbrev C := SU3DefiningExterior.Vector
abbrev W := WeakDoubletScalars.Doublet
abbrev colorProjection : Group →* SU3DefiningExterior.Group := MonoidHom.fst _ _
abbrev weakProjection : Group →* WeakDoubletScalars.Group := MonoidHom.snd _ _
abbrev color : Representation ℂ Group C := SU3DefiningExterior.rho.comp colorProjection
abbrev weak : Representation ℂ Group W := WeakDoubletScalars.doublet.comp weakProjection
abbrev gauge : Representation ℂ Group (C ⊗[ℂ] W) := color.tprod weak
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup (C ⊗[ℂ] W) := inferInstance
def basis := SU3DefiningExterior.basis.tensorProduct (Pi.basisFun ℂ (Fin 2))

abbrev adjoint := TraceEndomorphismSplit.traceFreeAction color
abbrev harmonic := SymmetricSquareContractionRepresentation.action color
abbrev dualHarmonic := SymmetricSquareContractionRepresentation.action color.dual
abbrev cubicKernel := SymmetricCubeContractionRepresentation.action color
abbrev balancedKernel := SymmetricSquarePartialTraceRepresentation.action color
abbrev scalar := trivial ℂ Group ℂ
abbrev spin (n : ℕ) := weak.symmetricPower n

def colorTwo : Representation.Equiv (color.exteriorPower 2) color.dual :=
  restrictEquiv SU3DefiningExterior.twoEquiv colorProjection

def dualColorTwo : Representation.Equiv (color.dual.exteriorPower 2) color :=
  restrictEquiv SU3DualExterior.twoEquiv colorProjection

def colorTop : Representation.Equiv (color.exteriorPower 3) scalar :=
  restrictEquiv SU3DefiningExterior.topEquiv colorProjection

def colorHook : Representation.Equiv (ExteriorCubeHookRepresentation.action color) adjoint :=
  restrictEquiv SU3ColorHook.equivalence colorProjection

theorem color_dimension : Module.finrank ℂ C=3 := SU3DefiningExterior.dimension
theorem color_det (g : Group) : LinearMap.det (color g)=1 := SU3DefiningExterior.determinant g.1

def square : Representation.Equiv (gauge.exteriorPower 2)
    ((color.dual.tprod (spin 2)).prod (color.symmetricPower 2)) :=
  ColorWeakQuartic.square color weakProjection colorTwo

def cube : Representation.Equiv (gauge.exteriorPower 3)
    ((spin 3).prod (adjoint.tprod weak)) :=
  ColorWeakQuartic.cube color weakProjection colorTop colorHook

def fourth : Representation.Equiv (gauge.exteriorPower 4)
    ((color.tprod (spin 2)).prod (color.dual.symmetricPower 2)) :=
  ColorWeakQuartic.fourth color weakProjection colorTwo color_dimension color_det

theorem dimension : Module.finrank ℂ (C ⊗[ℂ] W)=6 :=
  ColorWeakQuartic.gauge_dimension (A := C) color_dimension

theorem determinant (g : Group) : LinearMap.det (gauge g)=1 :=
  ColorWeakQuartic.gauge_determinant color weakProjection color_det g

def complement {k l : ℕ} (h : k+l=6) :
    Representation.Equiv (gauge.exteriorPower k) (gauge.exteriorPower l).dual :=
  ComplementaryExteriorDuality.equiv gauge determinant
    (Module.Basis.exteriorPowerTopEquiv (Module.finBasis ℂ (C ⊗[ℂ] W))) (by rw [dimension]; exact h)

def weakSelfDual : Representation.Equiv weak weak.dual :=
  restrictEquiv SU2DoubletDuality.equivalence weakProjection

def fifth : Representation.Equiv (gauge.exteriorPower 5) (color.dual.tprod weak) :=
  (complement (by rfl : 5+1=6)).trans
    ((dualEquiv gauge.exteriorPowerOneEquiv).trans
      ((InvariantTensorCurry.tensorDual color weak).symm.trans
        (tensorEquiv (.refl color.dual) weakSelfDual.symm)))

def scalarDual : Representation.Equiv scalar.dual scalar where
  toLinearEquiv := LinearMap.ringLmapEquivSelf ℂ ℂ ℂ
  isIntertwining' _ := rfl

def sixth : Representation.Equiv (gauge.exteriorPower 6) scalar :=
  (complement (by rfl : 6+0=6)).trans
    ((dualEquiv gauge.exteriorPowerZeroEquiv).trans scalarDual)

def adjointDual : Representation.Equiv (adjoint.tprod color.dual)
    (dualHarmonic.prod ((color.symmetricPower 2).prod color.dual)) :=
  restrictEquiv SU3MiddleColor.adjointDual colorProjection

def adjointSquare : Representation.Equiv (adjoint.tprod (color.symmetricPower 2))
    (cubicKernel.prod (dualHarmonic.prod ((color.symmetricPower 2).prod color.dual))) :=
  restrictEquiv SU3MiddleColor.adjointSquare colorProjection

def adjointPair : Representation.Equiv (adjoint.tprod adjoint)
    (((scalar.prod adjoint).prod adjoint).prod
      (((color.symmetricPower 3).prod (color.dual.symmetricPower 3)).prod balancedKernel)) :=
  restrictEquiv SU3MiddleColor.adjointPair colorProjection

theorem color_coefficients : BasisActionContinuity.Coefficients
    SU3DefiningExterior.basis color := by
  intro i j
  have hc : Continuous (fun g : Group => (g.1 : Matrix (Fin 3) (Fin 3) ℂ) j i) :=
    (show Continuous (fun m : Matrix (Fin 3) (Fin 3) ℂ => m j i) from
      (continuous_apply i).comp (continuous_apply j)).comp
        (continuous_subtype_val.comp continuous_fst)
  simpa [color, SU3DefiningExterior.rho, SU3DefiningExterior.basis,
    SmallSpecialUnitary.defining, Matrix.toLin'_apply, Pi.basisFun_apply] using hc

theorem weak_coefficients : BasisActionContinuity.Coefficients (Pi.basisFun ℂ (Fin 2)) weak :=
  BasisActionContinuity.comp _ WeakDoubletScalars.doublet
    SU2ExteriorSliceModels.doublet_coefficients weakProjection continuous_snd

theorem gauge_coefficients : BasisActionContinuity.Coefficients basis gauge :=
  BasisActionContinuity.tensor _ _ _ _ color_coefficients weak_coefficients

abbrev model (n : ℕ) := SU2ExteriorSliceModels.action gauge basis n
abbrev modelEquiv (n : ℕ) := SU2ExteriorSliceModels.equivalence gauge basis n

theorem model_continuous (n : ℕ) : ContinuousRepresentationScope.IsJointlyContinuous (model n) :=
  SU2ExteriorSliceModels.continuous gauge basis
    (SU2ExteriorSliceModels.field_coefficients gauge basis gauge_coefficients) n

theorem model_bound (n : ℕ) : BoundedTorusWeights.Bounded
    (ProductFactorization.firstRestriction (model n)) TauCeti.SU2.torusHom (min n (12-n)) := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    SU2ExteriorSliceModels.model_bound gauge basis n

end
end Math.ColorWeakMiddleGauge
