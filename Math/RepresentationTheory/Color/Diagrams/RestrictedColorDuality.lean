import Math.RepresentationTheory.Symmetric.SymmetricPowerDualEquivalence
import Math.RepresentationTheory.Color.Diagrams.RestrictedColorTraces
import Math.RepresentationTheory.Decomposition.KernelDualComparison
import Math.RepresentationTheory.Coefficients.TraceFreeCoefficientExclusion

/-! Actual duals of the bounded contraction kernels are the corresponding
kernels for contragredient color. Source duality and finite cancellation
replace a supplied highest-weight or irreducibility classification. -/
namespace Math.RestrictedColorDuality
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (rho : Representation ℂ G V)

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (Sym[ℂ]^n A) := Module.addCommMonoidToAddCommGroup ℂ

def singleSource (p : ℕ) : Representation.Equiv
    ((rho.symmetricPower p).tprod rho.dual).dual
      ((rho.dual.symmetricPower p).tprod rho.dual.dual) :=
  (InvariantTensorCurry.tensorDual (rho.symmetricPower p) rho.dual).symm.trans
    (tensorEquiv (SymmetricPowerDualEquivalence.equivalence rho p).symm (.refl rho.dual.dual))

def doubleSource (p q : ℕ) : Representation.Equiv
    ((rho.symmetricPower p).tprod (rho.dual.symmetricPower q)).dual
      ((rho.dual.symmetricPower p).tprod (rho.dual.dual.symmetricPower q)) :=
  (InvariantTensorCurry.tensorDual (rho.symmetricPower p) (rho.dual.symmetricPower q)).symm.trans
    (tensorEquiv (SymmetricPowerDualEquivalence.equivalence rho p).symm
      (SymmetricPowerDualEquivalence.equivalence rho.dual q).symm)

def square : Representation.Equiv
    (SymmetricSquareContractionRepresentation.action rho).dual
      (SymmetricSquareContractionRepresentation.action rho.dual) :=
  KernelDualComparison.equivalence
    (r := SymmetricSquareContractionRepresentation.source rho) (q := rho)
    (k := SymmetricSquareContractionRepresentation.action rho)
    (s := SymmetricSquareContractionRepresentation.source rho.dual) (t := rho.dual)
    (l := SymmetricSquareContractionRepresentation.action rho.dual)
    (SymmetricSquareContractionRepresentation.equivalence rho)
    (SymmetricSquareContractionRepresentation.equivalence rho.dual)
    (singleSource rho 2) (.refl rho.dual)

def cube : Representation.Equiv
    (SymmetricCubeContractionRepresentation.action rho).dual
      (SymmetricCubeContractionRepresentation.action rho.dual) :=
  KernelDualComparison.equivalence
    (r := SymmetricCubeContractionRepresentation.source rho) (q := rho.symmetricPower 2)
    (k := SymmetricCubeContractionRepresentation.action rho)
    (s := SymmetricCubeContractionRepresentation.source rho.dual) (t := rho.dual.symmetricPower 2)
    (l := SymmetricCubeContractionRepresentation.action rho.dual)
    (SymmetricCubeContractionRepresentation.equivalence rho)
    (SymmetricCubeContractionRepresentation.equivalence rho.dual)
    (singleSource rho 3) (SymmetricPowerDualEquivalence.equivalence rho 2).symm

def squareSquare : Representation.Equiv
    (SymmetricSquarePartialTraceRepresentation.action rho).dual
      (SymmetricSquarePartialTraceRepresentation.action rho.dual) :=
  KernelDualComparison.equivalence
    (r := SymmetricSquarePartialTraceRepresentation.source rho) (q := rho.tprod rho.dual)
    (k := SymmetricSquarePartialTraceRepresentation.action rho)
    (s := SymmetricSquarePartialTraceRepresentation.source rho.dual) (t := rho.dual.tprod rho.dual.dual)
    (l := SymmetricSquarePartialTraceRepresentation.action rho.dual)
    (SymmetricSquarePartialTraceRepresentation.equivalence rho)
    (SymmetricSquarePartialTraceRepresentation.equivalence rho.dual)
    (doubleSource rho 2 2) (InvariantTensorCurry.tensorDual rho rho.dual).symm

def scalarDual : Representation.Equiv (trivial ℂ G ℂ).dual (trivial ℂ G ℂ) where
  toLinearEquiv := LinearMap.ringLmapEquivSelf ℂ ℂ ℂ
  isIntertwining' _ := rfl

def endomorphismSource : Representation.Equiv (TraceEndomorphismSplit.action rho).dual
    (TraceEndomorphismSplit.action rho.dual) :=
  (SplitRepresentationProjection.dualEquiv (TraceFreeCoefficientExclusion.tensorEnd rho)).symm.trans
    ((InvariantTensorCurry.tensorDual rho rho.dual).symm.trans
      (TraceFreeCoefficientExclusion.tensorEnd rho.dual))

def adjoint (hd : Module.finrank ℂ V ≠ 0) : Representation.Equiv
    (TraceEndomorphismSplit.traceFreeAction rho).dual
      (TraceEndomorphismSplit.traceFreeAction rho.dual) :=
  KernelDualComparison.equivalence
    (TraceEndomorphismSplit.equivalence rho hd).symm
    (TraceEndomorphismSplit.equivalence rho.dual (by rw [Subspace.dual_finrank_eq]; exact hd)).symm
    (endomorphismSource rho) scalarDual

end
end Math.RestrictedColorDuality
