import Math.RepresentationTheory.SU2.SU2ConsecutiveSlices
import Math.RepresentationTheory.SU2.SU2IsotypicModels
import Math.RepresentationTheory.Constructions.FiniteExternalProducts

/-! Consecutive actual weight slices for any continuous finite-dimensional
SU2 x K representation with a proved weight bound. The complete isotypic
decomposition is constructed, not supplied as a new branching premise. -/
namespace Math.SU2IsotypicSlices
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor TorusWeightSlice
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance

def modelEquivalence (m : ℕ) : Representation.Equiv
    (WeakDoubletScalars.doublet.symmetricPower m) (SU2IsotypicEvaluation.model m) := by
  rw [WeakDoubletScalars.symmetricPower_eq]
  exact TauCeti.SU2.symPowerModelEquiv m

variable {K V : Type*} [Group K] [TopologicalSpace K]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (rho : Representation ℂ (WeakDoubletScalars.Group × K) V) (N : ℕ)
  (hr : ContinuousRepresentationScope.IsJointlyContinuous rho)
  (hb : BoundedTorusWeights.Bounded (ProductFactorization.firstRestriction rho)
    TauCeti.SU2.torusHom N)
abbrev multiplicity (i : Fin (N+1)) := SU2IsotypicModels.action rho i.val
abbrev M (i : Fin (N+1)) := SU2IsotypicModels.Carrier rho i.val
abbrev degree (i : Fin (N+1)) := i.val
@[reducible] local instance (i : Fin (N+1)) :
    AddCommGroup (Sym[ℂ]^i.val WeakDoubletScalars.Doublet) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance (i : Fin (N+1)) : AddCommGroup
    ((Sym[ℂ]^i.val WeakDoubletScalars.Doublet) ⊗[ℂ] M rho N i) := inferInstance

def pieceEquivalence (i : Fin (N+1)) : Representation.Equiv
    (SU2StringSliceSum.piece (multiplicity rho N) (degree N) i) (SU2IsotypicModels.piece rho N i) where
  toLinearEquiv := TensorProduct.congr (modelEquivalence i.val).toLinearEquiv (.refl ℂ _)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    exact congrArg (fun z => z ⊗ₜ[ℂ] multiplicity rho N i g.2 y)
      ((modelEquivalence i.val).isIntertwining _ _ g.1 x)

abbrev source := SU2StringSliceSum.source (multiplicity rho N) (degree N)

def sourceEquivalence : Representation.Equiv (source rho N) rho :=
  (FiniteExternalProducts.along (pieceEquivalence rho N)).trans
    (SU2IsotypicModels.ofBound rho N hr hb)

/-- The actual weight-k space is the entire color/weak multiplicity at k
plus the next actual weight space. Both directions preserve the K action. -/
def equivalence (k : Fin (N+1)) : Representation.Equiv
    (action rho TauCeti.SU2.torusHom (k.val : ℤ))
    ((multiplicity rho N k).prod (action rho TauCeti.SU2.torusHom ((k.val : ℤ)+2))) :=
  (transport rho TauCeti.SU2.torusHom (sourceEquivalence rho N hr hb).symm (k.val : ℤ)).trans
    ((SU2ConsecutiveSlices.equivalence N (multiplicity rho N) k).trans
      (SplitRepresentationProjection.prodEquiv (.refl _)
        (transport (source rho N) TauCeti.SU2.torusHom
          (sourceEquivalence rho N hr hb) ((k.val : ℤ)+2))))

end
end Math.SU2IsotypicSlices
