import Math.RepresentationTheory.Exterior.ExteriorCubeDoubletCauchy
import Math.RepresentationTheory.Color.SU3.SU3DoubleSpinSquare
import Math.RepresentationTheory.Color.SU3.SU3DoubleSpinExterior
import Math.RepresentationTheory.Color.SU3.SU3SpinExteriorCube
import Math.RepresentationTheory.Color.SU3.SU3ConjugateSpinExteriorCube

/-! A complete coarse Q cube split, resolving its top column into actual
scalar/trace-free color branches. The remaining color/weak hook is an
actual kernel representation, not yet a resolved color Young decomposition. -/
namespace Math.SU3DoubleSpinCube
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SU3DoubleSpinSquare
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
@[reducible] local instance : AddCommGroup (Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ Color ⊗[ℂ] Doublet) := inferInstance

def colorWeakProjection : Group →* SU3SpinExterior.Group where
  toFun g := (g.1,g.2.1)
  map_one' := rfl
  map_mul' _ _ := rfl

abbrev colorWeak := color.tprod weak
abbrev dualColorWeak := color.dual.tprod weak
abbrev weakTop := weak.symmetricPower 3
abbrev adjointWeak : Representation ℂ Group
    (TraceEndomorphismSplit.TraceFree SU3DefiningExterior.rho ⊗[ℂ] Doublet) :=
  SU3SpinExteriorCube.middleBranch.comp colorWeakProjection
abbrev dualAdjointWeak : Representation ℂ Group
    (TraceEndomorphismSplit.TraceFree SU3DefiningExterior.rho.dual ⊗[ℂ] Doublet) :=
  SU3ConjugateSpinExteriorCube.middleBranch.comp colorWeakProjection
abbrev first := weakTop.tprod (spin.symmetricPower 3)
abbrev second := adjointWeak.tprod (spin.symmetricPower 3)
abbrev dualSecond := dualAdjointWeak.tprod (spin.symmetricPower 3)
abbrev remainder := ExteriorCubeDoubletRepresentation.middle colorWeak spinProjection
abbrev dualRemainder := ExteriorCubeDoubletRepresentation.middle dualColorWeak spinProjection
abbrev branches := (first.prod second).prod remainder
abbrev dualBranches := (first.prod dualSecond).prod dualRemainder

@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Hook (V := Color ⊗[ℂ] Doublet)) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Hook (V := Module.Dual ℂ Color ⊗[ℂ] Doublet)) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (Sym[ℂ]^3 Doublet ⊗[ℂ] Sym[ℂ]^3 Doublet) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (TraceEndomorphismSplit.TraceFree SU3DefiningExterior.rho ⊗[ℂ] Doublet) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (TraceEndomorphismSplit.TraceFree SU3DefiningExterior.rho.dual ⊗[ℂ] Doublet) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup ((TraceEndomorphismSplit.TraceFree SU3DefiningExterior.rho ⊗[ℂ] Doublet) ⊗[ℂ] Sym[ℂ]^3 Doublet) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup ((TraceEndomorphismSplit.TraceFree SU3DefiningExterior.rho.dual ⊗[ℂ] Doublet) ⊗[ℂ] Sym[ℂ]^3 Doublet) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Hook (V := Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Hook (V := Module.Dual ℂ Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := Module.addCommMonoidToAddCommGroup ℂ

def colorWeakCube : Representation.Equiv (colorWeak.exteriorPower 3) (weakTop.prod adjointWeak) where
  toLinearEquiv := SU3SpinExteriorCube.cubeEquiv.toLinearEquiv
  isIntertwining' g := SU3SpinExteriorCube.cubeEquiv.isIntertwining' (colorWeakProjection g)

def dualColorWeakCube : Representation.Equiv (dualColorWeak.exteriorPower 3)
    (weakTop.prod dualAdjointWeak) where
  toLinearEquiv := SU3ConjugateSpinExteriorCube.cubeEquiv.toLinearEquiv
  isIntertwining' g := SU3ConjugateSpinExteriorCube.cubeEquiv.isIntertwining' (colorWeakProjection g)

variable {V W X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]
def prodLeft (a : Representation ℂ Group V) (b : Representation ℂ Group W)
    (c : Representation ℂ Group X) : Representation.Equiv
    ((a.prod b).tprod c) ((a.tprod c).prod (b.tprod c)) where
  toLinearEquiv := TensorProduct.prodLeft ℂ ℂ V W X
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    apply Prod.ext <;> rfl

def topEquiv : Representation.Equiv
    (ExteriorCubeDoubletCauchyRepresentation.top colorWeak spinProjection) (first.prod second) :=
  (tensorEquiv colorWeakCube (.refl (spin.symmetricPower 3))).trans
    (prodLeft weakTop adjointWeak (spin.symmetricPower 3))

def dualTopEquiv : Representation.Equiv
    (ExteriorCubeDoubletCauchyRepresentation.top dualColorWeak spinProjection) (first.prod dualSecond) :=
  (tensorEquiv dualColorWeakCube (.refl (spin.symmetricPower 3))).trans
    (prodLeft weakTop dualAdjointWeak (spin.symmetricPower 3))

/-- Exhaustive coarse split; the hook branch still requires color/weak resolution. -/
def positive : Representation.Equiv (tensor.exteriorPower 3) branches :=
  (ExteriorCubeDoubletCauchyRepresentation.equivalence colorWeak spinProjection).symm.trans
    (SplitRepresentationProjection.prodEquiv topEquiv (.refl remainder))

def negative : Representation.Equiv (dualTensor.exteriorPower 3) dualBranches :=
  (ExteriorCubeDoubletCauchyRepresentation.equivalence dualColorWeak spinProjection).symm.trans
    (SplitRepresentationProjection.prodEquiv dualTopEquiv (.refl dualRemainder))

def positiveNine : Representation.Equiv (tensor.exteriorPower 9) branches.dual :=
  (SU3DoubleSpinExterior.complement (by rfl : 9+3=12)).trans
    (SplitRepresentationProjection.dualEquiv positive)

def negativeNine : Representation.Equiv (dualTensor.exteriorPower 9) dualBranches.dual :=
  (SU3DoubleSpinExterior.dualComplement (by rfl : 9+3=12)).trans
    (SplitRepresentationProjection.dualEquiv negative)

end
end Math.SU3DoubleSpinCube
