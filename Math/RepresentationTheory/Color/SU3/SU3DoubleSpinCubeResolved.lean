import Math.RepresentationTheory.Exterior.ExteriorCubeDoubletHook
import Math.RepresentationTheory.Color.SU3.SU3DoubleSpinCube

/-! Fully labelled actual Q cubic branches, including the color/weak hook.
Finite-length cancellation resolves the hook without an assumed Schur
branching theorem or an irreducibility premise for its color components. -/
namespace Math.SU3DoubleSpinCubeResolved
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection SU3DoubleSpinSquare
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
@[reducible] local instance : AddCommGroup (Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ Color ⊗[ℂ] Doublet) := inferInstance

abbrev adjoint : Representation ℂ Group (TraceEndomorphismSplit.TraceFree SU3DefiningExterior.rho) :=
  SU3ColorPair.adjoint.comp (MonoidHom.fst _ _)
abbrev dualAdjoint : Representation ℂ Group (TraceEndomorphismSplit.TraceFree SU3DualExterior.rho) :=
  (TraceEndomorphismSplit.traceFreeAction SU3DualExterior.rho).comp (MonoidHom.fst _ _)

def colorTop : Representation.Equiv (color.exteriorPower 3) (trivial ℂ Group ℂ) where
  toLinearEquiv := SU3DefiningExterior.topEquiv.toLinearEquiv
  isIntertwining' g := SU3DefiningExterior.topEquiv.isIntertwining' g.1

def dualColorTop : Representation.Equiv (color.dual.exteriorPower 3) (trivial ℂ Group ℂ) where
  toLinearEquiv := SU3DualExterior.topEquiv.toLinearEquiv
  isIntertwining' g := SU3DualExterior.topEquiv.isIntertwining' g.1

def colorHook : Representation.Equiv (ExteriorCubeHookRepresentation.action color) adjoint where
  toLinearEquiv := SU3ColorHook.equivalence.toLinearEquiv
  isIntertwining' g := SU3ColorHook.equivalence.isIntertwining' g.1

def dualColorHook : Representation.Equiv (ExteriorCubeHookRepresentation.action color.dual) dualAdjoint where
  toLinearEquiv := SU3DualColorHook.equivalence.toLinearEquiv
  isIntertwining' g := SU3DualColorHook.equivalence.isIntertwining' g.1

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
  (r : Representation ℂ Group V) (t : Representation ℂ Group W)
abbrev hookBranches := (weak.prod (t.tprod (weak.symmetricPower 3))).prod
  (((r.symmetricPower 3).tprod weak).prod (t.tprod weak))
abbrev spinBranches := ((weak.tprod spin).prod ((t.tprod (weak.symmetricPower 3)).tprod spin)).prod
  ((((r.symmetricPower 3).tprod weak).tprod spin).prod ((t.tprod weak).tprod spin))

def resolve (ht : Representation.Equiv (r.exteriorPower 3) (trivial ℂ Group ℂ))
    (hh : Representation.Equiv (ExteriorCubeHookRepresentation.action r) t) :
    Representation.Equiv (ExteriorCubeDoubletHook.branches r weakProjection) (hookBranches r t) :=
  prodEquiv
    (prodEquiv ((tensorEquiv ht (.refl weak)).trans (Representation.TensorProduct.lid ℂ weak))
      (tensorEquiv hh (.refl (weak.symmetricPower 3))))
    (prodEquiv (.refl ((r.symmetricPower 3).tprod weak)) (tensorEquiv hh (.refl weak)))

def hookEquivalence [FiniteDimensional ℂ V]
    (ht : Representation.Equiv (r.exteriorPower 3) (trivial ℂ Group ℂ))
    (hh : Representation.Equiv (ExteriorCubeHookRepresentation.action r) t) :
    Representation.Equiv (ExteriorCubeHookRepresentation.action (r.tprod weak)) (hookBranches r t) :=
  (ExteriorCubeDoubletHook.equivalence r weakProjection).trans (resolve r t ht hh)

def distribute : Representation.Equiv ((hookBranches r t).tprod spin) (spinBranches r t) :=
  (TensorProductSums.prodLeft (weak.prod (t.tprod (weak.symmetricPower 3)))
    (((r.symmetricPower 3).tprod weak).prod (t.tprod weak)) spin).trans
      (prodEquiv (TensorProductSums.prodLeft weak (t.tprod (weak.symmetricPower 3)) spin)
        (TensorProductSums.prodLeft ((r.symmetricPower 3).tprod weak) (t.tprod weak) spin))

abbrev positiveBranches := (SU3DoubleSpinCube.first.prod SU3DoubleSpinCube.second).prod
  (spinBranches color adjoint)
abbrev negativeBranches := (SU3DoubleSpinCube.first.prod SU3DoubleSpinCube.dualSecond).prod
  (spinBranches color.dual dualAdjoint)

def positiveRest : Representation.Equiv SU3DoubleSpinCube.remainder (spinBranches color adjoint) :=
  (tensorEquiv (hookEquivalence color adjoint colorTop colorHook) (.refl spin)).trans
    (distribute color adjoint)

def negativeRest : Representation.Equiv SU3DoubleSpinCube.dualRemainder (spinBranches color.dual dualAdjoint) :=
  (tensorEquiv (hookEquivalence color.dual dualAdjoint dualColorTop dualColorHook) (.refl spin)).trans
    (distribute color.dual dualAdjoint)

/-- All six cubic Q branches with color, weak and spin actions retained. -/
def positive : Representation.Equiv (tensor.exteriorPower 3) positiveBranches :=
  SU3DoubleSpinCube.positive.trans (prodEquiv (.refl _) positiveRest)

def negative : Representation.Equiv (dualTensor.exteriorPower 3) negativeBranches :=
  SU3DoubleSpinCube.negative.trans (prodEquiv (.refl _) negativeRest)

def positiveNine : Representation.Equiv (tensor.exteriorPower 9) positiveBranches.dual :=
  (SU3DoubleSpinExterior.complement (by rfl : 9+3=12)).trans (dualEquiv positive)

def negativeNine : Representation.Equiv (dualTensor.exteriorPower 9) negativeBranches.dual :=
  (SU3DoubleSpinExterior.dualComplement (by rfl : 9+3=12)).trans (dualEquiv negative)

end
end Math.SU3DoubleSpinCubeResolved
