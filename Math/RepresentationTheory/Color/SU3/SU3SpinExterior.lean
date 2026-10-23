import TauCeti.LinearAlgebra.ExteriorPower.Basis
import Math.RepresentationTheory.Exterior.ExteriorSquareCauchy
import Math.RepresentationTheory.Color.SU3.SU3DefiningExterior
import Math.RepresentationTheory.SU2.WeakDoubletScalars
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection
import Math.LinearAlgebra.Tensor.TensorDeterminant

/-! Actual colored/spin exterior branches. The square decomposition is
complete by explicit Cauchy inverse maps, not by color irreducibility or
numerical dimensions. U(1) and residual twists are not part of this group. -/
namespace Math.SU3SpinExterior
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct
abbrev Group := SU3DefiningExterior.Group × WeakDoubletScalars.Group
abbrev Color := SU3DefiningExterior.Vector
abbrev Spin := WeakDoubletScalars.Doublet
abbrev color : Representation ℂ Group Color := SU3DefiningExterior.rho.comp (MonoidHom.fst _ _)
abbrev spin : Representation ℂ Group Spin := WeakDoubletScalars.doublet.comp (MonoidHom.snd _ _)
abbrev tensor := color.tprod spin

@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance

abbrev firstBranch := external SU3DefiningExterior.rho.dual (WeakDoubletScalars.doublet.symmetricPower 2)
abbrev secondBranch := color.symmetricPower 2

@[reducible] local instance : AddCommGroup (ExteriorSquareCauchy.First (A := Color) (B := Spin)) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorSquareCauchy.Second (A := Color) (B := Spin)) := inferInstance

def firstEquiv : Representation.Equiv
    (ExteriorSquareCauchyRepresentation.firstAction color spin) firstBranch where
  toLinearEquiv := TensorProduct.congr SU3DefiningExterior.twoEquiv.toLinearEquiv (.refl ℂ _)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    exact congrArg (fun z => z ⊗ₜ[ℂ] (WeakDoubletScalars.doublet.symmetricPower 2) g.2 y)
      (SU3DefiningExterior.twoEquiv.isIntertwining _ _ g.1 x)

def spinBasis := Pi.basisFun ℂ (Fin 2)

theorem color_det (g : Group) : LinearMap.det (color g)=1 := SU3DefiningExterior.determinant g.1

theorem spin_det (g : Group) : LinearMap.det (spin g)=1 := by
  change LinearMap.det (Matrix.toLin' (g.2 : Matrix (Fin 2) (Fin 2) ℂ))=1
  rw [LinearMap.det_toLin']
  exact g.2.prop.2

def spinTop : Representation.Equiv (spin.exteriorPower 2) (trivial ℂ Group ℂ) where
  toLinearEquiv := Module.Basis.exteriorPowerTopEquiv spinBasis
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change Module.Basis.exteriorPowerTopEquiv spinBasis (exteriorPower.map 2 (spin g) x)=
      Module.Basis.exteriorPowerTopEquiv spinBasis x
    rw [Module.Basis.map_exteriorPower_top_eq_det_smul spinBasis,spin_det g,one_smul]
    rfl

def secondEquiv : Representation.Equiv
    (ExteriorSquareCauchyRepresentation.secondAction color spin) secondBranch :=
  (tensorEquiv (.refl (color.symmetricPower 2)) spinTop).trans
    { toLinearEquiv := TensorProduct.rid ℂ (Sym[ℂ]^2 Color)
      isIntertwining' g := by
        apply TensorProduct.ext'
        intro x z
        change z • (color.symmetricPower 2) g x=(color.symmetricPower 2) g (z • x)
        exact (map_smul _ z x).symm }

/-- Both colored/spin square branches are retained, with no matching premise. -/
def squareEquiv : Representation.Equiv (tensor.exteriorPower 2) (firstBranch.prod secondBranch) :=
  (ExteriorSquareCauchyRepresentation.equivalence color spin).trans
    (SplitRepresentationProjection.prodEquiv firstEquiv secondEquiv)

theorem tensor_dimension : Module.finrank ℂ (Color ⊗[ℂ] Spin)=6 := by
  rw [Module.finrank_tensorProduct,SU3DefiningExterior.dimension]
  norm_num [Spin,WeakDoubletScalars.Doublet]

theorem tensor_det (g : Group) : LinearMap.det (tensor g)=1 :=
  TensorDeterminant.map_one SU3DefiningExterior.basis spinBasis (color g) (spin g)
    (color_det g) (spin_det g)

def volume := Module.Basis.exteriorPowerTopEquiv (Module.finBasis ℂ (Color ⊗[ℂ] Spin))

def complement {n m : ℕ} (h : n+m=6) :
    Representation.Equiv (tensor.exteriorPower n) (tensor.exteriorPower m).dual :=
  ComplementaryExteriorDuality.equiv tensor tensor_det volume (by rw [tensor_dimension]; exact h)

def fourEquiv : Representation.Equiv (tensor.exteriorPower 4) (firstBranch.prod secondBranch).dual :=
  (complement (by rfl : 4+2=6)).trans (SplitRepresentationProjection.dualEquiv squareEquiv)

def fiveEquiv : Representation.Equiv (tensor.exteriorPower 5) tensor.dual :=
  (complement (by rfl : 5+1=6)).trans (SplitRepresentationProjection.dualEquiv tensor.exteriorPowerOneEquiv)

def tensorBasis : Module.Basis (Fin 6) ℂ (Color ⊗[ℂ] Spin) :=
  (SU3DefiningExterior.basis.tensorProduct spinBasis).reindex finProdFinEquiv

def sixEquiv : Representation.Equiv (tensor.exteriorPower 6) (trivial ℂ Group ℂ) where
  toLinearEquiv := Module.Basis.exteriorPowerTopEquiv tensorBasis
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change Module.Basis.exteriorPowerTopEquiv tensorBasis (exteriorPower.map 6 (tensor g) x)=Module.Basis.exteriorPowerTopEquiv tensorBasis x
    rw [Module.Basis.map_exteriorPower_top_eq_det_smul tensorBasis,tensor_det g,one_smul]
    rfl

theorem high_zero (n : ℕ) (hn : 6<n) (x : ⋀[ℂ]^n (Color ⊗[ℂ] Spin)) : x=0 :=
  exteriorPower.eq_zero_of_finrank_lt n (by rw [tensor_dimension]; exact hn) x

end
end Math.SU3SpinExterior
