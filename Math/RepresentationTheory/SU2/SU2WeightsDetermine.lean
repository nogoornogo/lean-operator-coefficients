import Math.RepresentationTheory.SU2.SU2IsotypicSlices
import Math.RepresentationTheory.Decomposition.FiniteSummandCancellation

/-! Actual retained-action weight spaces determine a bounded SU2
representation. Complete isotypic models and finite-length cancellation
prove the reconstruction, without dimensions or character subtraction. -/
namespace Math.SU2WeightsDetermine
set_option autoImplicit false
noncomputable section
open Representation TorusWeightSlice ExternalInvariantTensor SplitRepresentationProjection
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {K V : Type*} [Group K] [TopologicalSpace K]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (rho : Representation ℂ (WeakDoubletScalars.Group × K) V) (N : ℕ)
  (hr : ContinuousRepresentationScope.IsJointlyContinuous rho)
  (hb : BoundedTorusWeights.Bounded (ProductFactorization.firstRestriction rho)
    TauCeti.SU2.torusHom N)
  {U : Fin (N+1) → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
  (s : ∀ i, Representation ℂ K (U i))
@[reducible] local instance (i : Fin (N+1)) :
    AddCommGroup (Sym[ℂ]^i.val WeakDoubletScalars.Doublet) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance (i : Fin (N+1)) : AddCommGroup
    ((Sym[ℂ]^i.val WeakDoubletScalars.Doublet) ⊗[ℂ] U i) := inferInstance
abbrev candidate := SU2ConsecutiveSlices.total N s
variable (h : ∀ k : ℤ, 0≤k → k≤(N : ℤ)+2 →
  Representation.Equiv (action rho TauCeti.SU2.torusHom k)
    (action (candidate N s) TauCeti.SU2.torusHom k))

def multiplicity (i : Fin (N+1)) : Representation.Equiv
    (SU2IsotypicSlices.multiplicity rho N i) (s i) := by
  let e := ((SU2IsotypicSlices.equivalence rho N hr hb i).symm.trans
    (h i.val (by omega) (by have hi := i.isLt; omega))).trans
    ((SU2ConsecutiveSlices.equivalence N s i).trans
      (prodEquiv (.refl (s i))
        (h ((i.val : ℤ)+2) (by omega) (by have hi := i.isLt; omega)).symm))
  exact Classical.choice (FiniteSummandCancellation.nonempty_equiv
    (A := SU2IsotypicSlices.M rho N i) (B := U i)
    (C := Space rho TauCeti.SU2.torusHom ((i.val : ℤ)+2))
    (SU2IsotypicSlices.multiplicity rho N i) (s i)
    (action rho TauCeti.SU2.torusHom ((i.val : ℤ)+2)) e)

def piece (i : Fin (N+1)) : Representation.Equiv
    (SU2StringSliceSum.piece (SU2IsotypicSlices.multiplicity rho N)
      (SU2IsotypicSlices.degree N) i)
    (SU2StringSliceSum.piece s (SU2ConsecutiveSlices.degree N) i) where
  toLinearEquiv := TensorProduct.congr (.refl ℂ _)
    (multiplicity rho N hr hb s h i).toLinearEquiv
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    exact congrArg (fun z => WeakDoubletScalars.doublet.symmetricPower i.val g.1 x ⊗ₜ[ℂ] z)
      ((multiplicity rho N hr hb s h i).isIntertwining _ _ g.2 y)

/-- Reconstruction from finitely bounded actual weight-space comparisons.
The retained group need not be compact or semisimple. -/
def equivalence : Representation.Equiv rho (candidate N s) :=
  (SU2IsotypicSlices.sourceEquivalence rho N hr hb).symm.trans
    (FiniteExternalProducts.along (piece rho N hr hb s h))

end
end Math.SU2WeightsDetermine
