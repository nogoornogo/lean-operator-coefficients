import Math.RepresentationTheory.SU3QuarticColor
import Math.RepresentationTheory.SU3ColorHook
import Math.RepresentationTheory.SymmetricCubeContraction
import Math.RepresentationTheory.SymmetricSquarePartialTrace
import Math.RepresentationTheory.TraceFreeDualEnd
import Math.RepresentationTheory.SU3DualColorHook

/-! Actual color source identities for the middle Q degrees. Canonical
contraction kernels and finite summand cancellation replace any supplied
SU3 Young-branching comparison. -/
namespace Math.SU3MiddleColor
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open SU3DefiningExterior SU3ColorPair
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
abbrev square := rho.symmetricPower 2
abbrev cubic := rho.symmetricPower 3
abbrev cubicKernel := SymmetricCubeContractionRepresentation.action rho
abbrev balancedKernel := SymmetricSquarePartialTraceRepresentation.action rho
abbrev adjointSquareBranches := cubicKernel.prod
  (SU3QuarticColor.dualHarmonic.prod (square.prod rho.dual))
@[reducible] local instance : AddCommGroup Adjoint := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (Sym[ℂ]^2 Vector) := Module.addCommMonoidToAddCommGroup ℂ
abbrev AdjSquareCarrier := (SymmetricCubeContraction.Kernel (A := Vector)) ×
  ((SymmetricSquareContraction.Kernel (A := Module.Dual ℂ Vector)) ×
    ((Sym[ℂ]^2 Vector) × Module.Dual ℂ Vector))
@[reducible] local instance : AddCommGroup AdjSquareCarrier :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (Adjoint ⊗[ℂ] Sym[ℂ]^2 Vector) := inferInstance

theorem cubicKernel_nontrivial :
    Nontrivial (SymmetricCubeContraction.Kernel (A := Vector)) := by
  obtain ⟨x,hx⟩ := SymmetricCubeContraction.exists_kernel_ne_zero (A := Vector)
    (Pi.single (0 : Fin 3) (1 : ℂ)) (LinearMap.proj (1 : Fin 3))
    (by intro h; have he := congrFun h 0; simp at he)
    (by intro h; have he := DFunLike.congr_fun h (Pi.single (1 : Fin 3) 1); simp at he)
    (by simp)
  exact ⟨⟨x,0,hx⟩⟩

theorem dualCubicKernel_nontrivial :
    Nontrivial (SymmetricCubeContraction.Kernel (A := Module.Dual ℂ Vector)) := by
  obtain ⟨x,hx⟩ := SymmetricCubeContraction.exists_kernel_ne_zero (A := Module.Dual ℂ Vector)
    (LinearMap.proj (0 : Fin 3))
    (Module.Dual.eval ℂ Vector (Pi.single (1 : Fin 3) 1))
    (by intro h; have he := DFunLike.congr_fun h (Pi.single (0 : Fin 3) 1); simp at he)
    (by intro h; have he := DFunLike.congr_fun h (LinearMap.proj (1 : Fin 3)); simp at he)
    (by simp)
  exact ⟨⟨x,0,hx⟩⟩

theorem balancedKernel_nontrivial :
    Nontrivial (SymmetricSquarePartialTrace.Kernel (A := Vector)) := by
  obtain ⟨x,hx⟩ := SymmetricSquarePartialTrace.exists_kernel_ne_zero (A := Vector)
    (Pi.single (0 : Fin 3) (1 : ℂ)) (LinearMap.proj (1 : Fin 3))
    (by intro h; have he := congrFun h 0; simp at he)
    (by intro h; have he := DFunLike.congr_fun h (Pi.single (1 : Fin 3) 1); simp at he)
    (by simp)
  exact ⟨⟨x,0,hx⟩⟩

def definingSquare : Representation.Equiv (rho.tprod square) (cubic.prod adjoint) :=
  (SymmetricCubeHookRepresentation.equivalence rho).trans
    (prodEquiv (.refl _) SU3ColorHook.equivalence)

def adjointDual : Representation.Equiv (adjoint.tprod rho.dual)
    (SU3QuarticColor.dualHarmonic.prod (square.prod rho.dual)) :=
  (Representation.TensorProduct.comm adjoint rho.dual).trans
    ((tensorEquiv (.refl rho.dual) (TraceFreeDualEnd.equivalence rho dimension_nonzero)).trans
      SU3QuarticColor.dualDefiningAdjoint)

abbrev source := (rho.tprod square).tprod rho.dual

def sourceTrace : Representation.Equiv source (square.prod (adjoint.tprod square)) :=
  (tensorEquiv (Representation.TensorProduct.comm rho square) (.refl rho.dual)).trans
    ((Representation.TensorProduct.assoc square rho rho.dual).trans
    ((tensorEquiv (.refl square) SU3ColorPair.equivalence).trans
    ((TensorProductSums.prodRight square (trivial ℂ Group ℂ) adjoint).trans
      (prodEquiv (Representation.TensorProduct.rid ℂ square)
        (Representation.TensorProduct.comm square adjoint)))))

def sourceCubic : Representation.Equiv source
    ((square.prod cubicKernel).prod
      (SU3QuarticColor.dualHarmonic.prod (square.prod rho.dual))) :=
  (tensorEquiv definingSquare (.refl rho.dual)).trans
    ((TensorProductSums.prodLeft cubic adjoint rho.dual).trans
      (prodEquiv (SymmetricCubeContractionRepresentation.equivalence rho) adjointDual))

def sourceReorder : Representation.Equiv
    ((square.prod cubicKernel).prod
      (SU3QuarticColor.dualHarmonic.prod (square.prod rho.dual)))
    (adjointSquareBranches.prod square) where
  toLinearEquiv :=
    { toFun x := ((x.1.2,x.2),x.1.1)
      invFun x := ((x.2,x.1.1),x.1.2)
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := by ext x <;> rfl

/-- Complete adjoint/symmetric-square split from two actual decompositions
of the same source. The common square cancels by finite module length. -/
def adjointSquare : Representation.Equiv (adjoint.tprod square) adjointSquareBranches :=
  Classical.choice (FiniteSummandCancellation.nonempty_equiv
    (A := Adjoint ⊗[ℂ] Sym[ℂ]^2 Vector) (B := AdjSquareCarrier)
    (C := Sym[ℂ]^2 Vector) (adjoint.tprod square) adjointSquareBranches square
    (((TensorProductSums.prodComm (adjoint.tprod square) square).trans sourceTrace.symm).trans
      (sourceCubic.trans sourceReorder)))

def squareDualSquare : Representation.Equiv
    (square.tprod (rho.dual.symmetricPower 2))
    (((trivial ℂ Group ℂ).prod adjoint).prod balancedKernel) :=
  (SymmetricSquarePartialTraceRepresentation.equivalence rho).trans
    (prodEquiv SU3ColorPair.equivalence (.refl _))

def dualDefiningSquare : Representation.Equiv
    (rho.dual.tprod (rho.dual.symmetricPower 2))
    ((rho.dual.symmetricPower 3).prod adjoint) :=
  (SymmetricCubeHookRepresentation.equivalence rho.dual).trans
    (prodEquiv (.refl _) (SU3DualColorHook.equivalence.trans
      (TraceFreeDualEnd.equivalence rho dimension_nonzero).symm))

abbrev scalar := trivial ℂ Group ℂ
abbrev common := (scalar.prod adjoint).prod adjoint
abbrev adjointPairBranches := common.prod
  ((cubic.prod (rho.dual.symmetricPower 3)).prod balancedKernel)
abbrev CommonCarrier := (ℂ × Adjoint) × Adjoint
abbrev AdjPairCarrier := CommonCarrier ×
  (((Sym[ℂ]^3 Vector) × (Sym[ℂ]^3 (Module.Dual ℂ Vector))) ×
    SymmetricSquarePartialTrace.Kernel (A := Vector))
@[reducible] local instance : AddCommGroup CommonCarrier := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup AdjPairCarrier := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (Adjoint ⊗[ℂ] Adjoint) := inferInstance

def pairSourceTrace : Representation.Equiv (colorPair.tprod colorPair)
    ((scalar.prod adjoint).prod (adjoint.prod (adjoint.tprod adjoint))) :=
  (tensorEquiv SU3ColorPair.equivalence SU3ColorPair.equivalence).trans
    ((TensorProductSums.expand scalar adjoint scalar adjoint).trans
      (prodEquiv
        (prodEquiv (Representation.TensorProduct.lid ℂ scalar)
          (Representation.TensorProduct.lid ℂ adjoint))
        (prodEquiv (Representation.TensorProduct.rid ℂ adjoint) (.refl _))))

def pairSourceTraceReorder : Representation.Equiv
    ((scalar.prod adjoint).prod (adjoint.prod (adjoint.tprod adjoint)))
    ((adjoint.tprod adjoint).prod common) where
  toLinearEquiv :=
    { toFun x := (x.2.2,(x.1,x.2.1))
      invFun x := (x.2.1,(x.2.2,x.1))
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := by ext x <;> rfl

abbrev pairExpanded :=
  ((((scalar.prod adjoint).prod balancedKernel).prod (cubic.prod adjoint)).prod
    (((rho.dual.symmetricPower 3).prod adjoint).prod (scalar.prod adjoint)))

def pairSourceSquares : Representation.Equiv (colorPair.tprod colorPair) pairExpanded :=
  (regroupPairDiagonal rho rho rho.dual rho.dual).trans
    ((tensorEquiv
      ((SymmetricExteriorSquare.equivalence rho).trans (prodEquiv (.refl _) twoEquiv))
      ((SymmetricExteriorSquare.equivalence rho.dual).trans
        (prodEquiv (.refl _) SU3DualExterior.twoEquiv))).trans
    ((TensorProductSums.expand square rho.dual (rho.dual.symmetricPower 2) rho).trans
      (prodEquiv
        (prodEquiv squareDualSquare
          ((Representation.TensorProduct.comm square rho).trans definingSquare))
        (prodEquiv dualDefiningSquare
          ((Representation.TensorProduct.comm rho.dual rho).trans SU3ColorPair.equivalence)))))

def pairSourceSquaresReorder : Representation.Equiv pairExpanded (adjointPairBranches.prod common) where
  toLinearEquiv :=
    { toFun x := (((x.1.1.1,x.1.2.2),((x.1.2.1,x.2.1.1),x.1.1.2)),
        ((x.2.2.1,x.2.1.2),x.2.2.2))
      invFun x := (((x.1.1.1,x.1.2.2),(x.1.2.1.1,x.1.1.2)),
        ((x.1.2.1.2,x.2.1.2),(x.2.1.1,x.2.2)))
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := by ext x <;> rfl

/-- Complete adjoint tensor adjoint decomposition into actual scalar,
adjoint, cubic, dual-cubic and balanced-kernel summands. -/
def adjointPair : Representation.Equiv (adjoint.tprod adjoint) adjointPairBranches :=
  Classical.choice (FiniteSummandCancellation.nonempty_equiv
    (A := Adjoint ⊗[ℂ] Adjoint) (B := AdjPairCarrier) (C := CommonCarrier)
    (adjoint.tprod adjoint) adjointPairBranches common
    (((pairSourceTrace.trans pairSourceTraceReorder).symm).trans
      (pairSourceSquares.trans pairSourceSquaresReorder)))

end
end Math.SU3MiddleColor
