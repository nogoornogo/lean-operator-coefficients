import Math.RepresentationTheory.SU2.SU2IsotypicSlices
import Math.RepresentationTheory.Decomposition.FiniteSummandCancellation
import Math.RepresentationTheory.Decomposition.ZeroSummands

/-! Identify one entire retained multiplicity by an actual consecutive
weight-space split. No numerical multiplicity is calculated. -/
namespace Math.SU2IsotypicIdentify
set_option autoImplicit false
noncomputable section
open Representation TorusWeightSlice ExternalInvariantTensor
open scoped TensorProduct
variable {K V A : Type*} [Group K] [TopologicalSpace K]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup A] [Module ℂ A]
  (rho : Representation ℂ (WeakDoubletScalars.Group × K) V) (N : ℕ)
  (hr : ContinuousRepresentationScope.IsJointlyContinuous rho)
  (hb : BoundedTorusWeights.Bounded (ProductFactorization.firstRestriction rho)
    TauCeti.SU2.torusHom N) (k : Fin (N+1)) (s : Representation ℂ K A)

def equivalence (e : Representation.Equiv (action rho TauCeti.SU2.torusHom (k.val : ℤ))
    (s.prod (action rho TauCeti.SU2.torusHom ((k.val : ℤ)+2)))) :
    Representation.Equiv (SU2IsotypicSlices.multiplicity rho N k) s :=
  Classical.choice (FiniteSummandCancellation.nonempty_equiv
    (A := SU2IsotypicSlices.M rho N k) (B := A)
    (C := Space rho TauCeti.SU2.torusHom ((k.val : ℤ)+2))
    (SU2IsotypicSlices.multiplicity rho N k) s
    (action rho TauCeti.SU2.torusHom ((k.val : ℤ)+2))
    ((SU2IsotypicSlices.equivalence rho N hr hb k).symm.trans e))

include hr hb in
theorem zero (hz : ∀ x : Space rho TauCeti.SU2.torusHom (k.val : ℤ), x=0)
    (v : SU2IsotypicSlices.M rho N k) : v=0 := by
  let e := SU2IsotypicSlices.equivalence rho N hr hb k
  have h : e.symm (v,0)=e.symm 0 :=
    (hz _).trans (map_zero e.symm.toIntertwiningMap.toLinearMap).symm
  exact congrArg Prod.fst (e.symm.injective h)

def highest (e : Representation.Equiv (action rho TauCeti.SU2.torusHom (k.val : ℤ)) s)
    (hz : ∀ x : Space rho TauCeti.SU2.torusHom ((k.val : ℤ)+2), x=0) :
    Representation.Equiv (SU2IsotypicSlices.multiplicity rho N k) s :=
  equivalence rho N hr hb k s
    (e.trans (ZeroSummands.prodRight s
      (action rho TauCeti.SU2.torusHom ((k.val : ℤ)+2)) hz).symm)

@[reducible] local instance : AddCommGroup (Sym[ℂ]^k.val WeakDoubletScalars.Doublet) :=
  Module.addCommMonoidToAddCommGroup ℂ

def piece (e : Representation.Equiv (SU2IsotypicSlices.multiplicity rho N k) s) :
    Representation.Equiv
      (SU2StringSliceSum.piece (SU2IsotypicSlices.multiplicity rho N)
        (SU2IsotypicSlices.degree N) k)
      (external (WeakDoubletScalars.doublet.symmetricPower k.val) s) where
  toLinearEquiv := TensorProduct.congr (.refl ℂ _) e.toLinearEquiv
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    exact congrArg (fun z => WeakDoubletScalars.doublet.symmetricPower k.val g.1 x ⊗ₜ[ℂ] z)
      (e.isIntertwining _ _ g.2 y)

end
end Math.SU2IsotypicIdentify
