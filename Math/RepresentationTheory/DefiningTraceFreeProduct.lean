import Math.RepresentationTheory.SymmetricSquareContraction
import Math.RepresentationTheory.SymmetricExteriorSquare
import Math.RepresentationTheory.Decomposition.FiniteSummandCancellation
import Math.RepresentationTheory.Decomposition.TensorProductSums

/-! The defining representation tensor trace-free endomorphisms, resolved
using actual symmetric contraction and exterior duality. Cancellation is
applied to two constructed whole-source equivalences. -/
namespace Math.DefiningTraceFreeProduct
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {G A : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  [FiniteDimensional ℂ A] (r : Representation ℂ G A)
abbrev adjoint := TraceEndomorphismSplit.traceFreeAction r
abbrev harmonic := SymmetricSquareContractionRepresentation.action r
abbrev source := r.tprod (r.tprod r.dual)
abbrev target := r.tprod (adjoint r)
abbrev branches := (harmonic r).prod ((r.dual.symmetricPower 2).prod r)
abbrev BranchCarrier := (SymmetricSquareContraction.Kernel (A := A)) × ((Sym[ℂ]^2 (Module.Dual ℂ A)) × A)
@[reducible] local instance : AddCommGroup (BranchCarrier (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (A ⊗[ℂ] TraceEndomorphismSplit.TraceFree r) := inferInstance
variable (hd : Module.finrank ℂ A≠0)

def sourceTrace : Representation.Equiv (source r) (r.prod (target r)) :=
  (tensorEquiv (.refl r)
    ((SymmetricSquareContractionRepresentation.pairEnd r).trans
      (TraceEndomorphismSplit.equivalence r hd).symm)).trans
    ((TensorProductSums.prodRight r (trivial ℂ G ℂ) (adjoint r)).trans
      (prodEquiv (Representation.TensorProduct.rid ℂ r) (.refl _)))

variable (two : Representation.Equiv (r.exteriorPower 2) r.dual)
  (dualTwo : Representation.Equiv (r.dual.exteriorPower 2) r)

def sourceSquares : Representation.Equiv (source r)
    ((r.prod (harmonic r)).prod ((r.dual.symmetricPower 2).prod r)) :=
  (Representation.TensorProduct.assoc r r r.dual).symm.trans
    ((tensorEquiv (SymmetricExteriorSquare.equivalence r) (.refl r.dual)).trans
      ((TensorProductSums.prodLeft (r.symmetricPower 2) (r.exteriorPower 2) r.dual).trans
        (prodEquiv (SymmetricSquareContractionRepresentation.equivalence r)
          ((tensorEquiv two (.refl r.dual)).trans
            ((SymmetricExteriorSquare.equivalence r.dual).trans
              (prodEquiv (.refl _) dualTwo))))))

def reorder : Representation.Equiv
    ((r.prod (harmonic r)).prod ((r.dual.symmetricPower 2).prod r)) ((branches r).prod r) where
  toLinearEquiv :=
    { toFun x := ((x.1.2,x.2),x.1.1)
      invFun x := ((x.2,x.1.1),x.1.2)
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := by ext x <;> rfl

/-- The three actual color factors after removing the scalar endomorphism
line. The exterior dualities are supplied actual equivalences, not
unevaluated occurrence propositions. -/
def equivalence : Representation.Equiv (target r) (branches r) :=
  Classical.choice (FiniteSummandCancellation.nonempty_equiv
    (A := A ⊗[ℂ] TraceEndomorphismSplit.TraceFree r)
    (B := BranchCarrier (A := A)) (C := A) (target r) (branches r) r
    (((TensorProductSums.prodComm (target r) r).trans (sourceTrace r hd).symm).trans
      ((sourceSquares r two dualTwo).trans (reorder r))))

end
end Math.DefiningTraceFreeProduct
