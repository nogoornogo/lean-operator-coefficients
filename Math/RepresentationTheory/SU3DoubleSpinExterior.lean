import Math.RepresentationTheory.SU3DoubleSpinSquare
import Math.RepresentationTheory.InvariantTensorCurry
import Math.RepresentationTheory.SU2DoubletDuality

/-! Conjugate-input comparison, determinant and complementary Q-core
branches; the weak factor and the spin factor remain distinct. -/
namespace Math.SU3DoubleSpinExterior
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SU3DoubleSpinSquare
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup ((Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Module.Dual ℂ Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance
abbrev negativeInput := (color.tprod weak).dual.tprod spin

def weakSelfDual : Representation.Equiv weak weak.dual where
  toLinearEquiv := SU2DoubletDuality.equivalence.toLinearEquiv
  isIntertwining' g := SU2DoubletDuality.equivalence.isIntertwining' (weakProjection g)

def negativeInputEquiv : Representation.Equiv negativeInput dualTensor :=
  tensorEquiv ((InvariantTensorCurry.tensorDual color weak).symm.trans
    (tensorEquiv (.refl color.dual) weakSelfDual.symm)) (.refl spin)

def colorBasis := SU3DefiningExterior.basis
def dualColorBasis := SU3DualExterior.basis
def doubletBasis := Pi.basisFun ℂ (Fin 2)

theorem color_det (g : Group) : LinearMap.det (color g)=1 := SU3DefiningExterior.determinant g.1

theorem dual_color_det (g : Group) : LinearMap.det (color.dual g)=1 := SU3DualExterior.determinant g.1

theorem weak_det (g : Group) : LinearMap.det (weak g)=1 := by
  change LinearMap.det (Matrix.toLin' (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ))=1
  rw [LinearMap.det_toLin']
  exact g.2.1.prop.2

theorem spin_det (g : Group) : LinearMap.det (spin g)=1 := by
  change LinearMap.det (Matrix.toLin' (g.2.2 : Matrix (Fin 2) (Fin 2) ℂ))=1
  rw [LinearMap.det_toLin']
  exact g.2.2.prop.2

theorem tensor_det (g : Group) : LinearMap.det (tensor g)=1 :=
  TensorDeterminant.map_one (colorBasis.tensorProduct doubletBasis) doubletBasis
    ((color.tprod weak) g) (spin g)
    (TensorDeterminant.map_one colorBasis doubletBasis (color g) (weak g) (color_det g) (weak_det g))
    (spin_det g)

theorem dual_tensor_det (g : Group) : LinearMap.det (dualTensor g)=1 :=
  TensorDeterminant.map_one (dualColorBasis.tensorProduct doubletBasis) doubletBasis
    ((color.dual.tprod weak) g) (spin g)
    (TensorDeterminant.map_one dualColorBasis doubletBasis (color.dual g) (weak g)
      (dual_color_det g) (weak_det g)) (spin_det g)

theorem tensor_dimension : Module.finrank ℂ ((Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet)=12 := by
  rw [Module.finrank_tensorProduct,Module.finrank_tensorProduct,SU3DefiningExterior.dimension]
  norm_num [Doublet,WeakDoubletScalars.Doublet]

theorem dual_tensor_dimension :
    Module.finrank ℂ ((Module.Dual ℂ Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet)=12 := by
  rw [Module.finrank_tensorProduct,Module.finrank_tensorProduct,Subspace.dual_finrank_eq,
    SU3DefiningExterior.dimension]
  norm_num [Doublet,WeakDoubletScalars.Doublet]

def complement {n m : ℕ} (h : n+m=12) :
    Representation.Equiv (tensor.exteriorPower n) (tensor.exteriorPower m).dual :=
  ComplementaryExteriorDuality.equiv tensor tensor_det
    (exteriorPower.topEquiv (Module.finBasis ℂ ((Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet)))
    (by rw [tensor_dimension]; exact h)

def dualComplement {n m : ℕ} (h : n+m=12) :
    Representation.Equiv (dualTensor.exteriorPower n) (dualTensor.exteriorPower m).dual :=
  ComplementaryExteriorDuality.equiv dualTensor dual_tensor_det
    (exteriorPower.topEquiv (Module.finBasis ℂ ((Module.Dual ℂ Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet)))
    (by rw [dual_tensor_dimension]; exact h)

def positiveTen : Representation.Equiv (tensor.exteriorPower 10)
    ((first color.dual).prod (second color)).dual :=
  (complement (by rfl : 10+2=12)).trans (SplitRepresentationProjection.dualEquiv positive)

def negativeTen : Representation.Equiv (dualTensor.exteriorPower 10)
    ((first color).prod (second color.dual)).dual :=
  (dualComplement (by rfl : 10+2=12)).trans (SplitRepresentationProjection.dualEquiv negative)

end
end Math.SU3DoubleSpinExterior
