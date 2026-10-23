import Math.RepresentationTheory.SU2.SU2IsotypicModels
import Math.RepresentationTheory.Decomposition.ExternalIrreducibleMatch
import Math.RepresentationTheory.Constructions.FiniteProductHomSupport
import Math.LinearAlgebra.Symmetric.SymmetricPowerLowDegree

/-! Eliminate every first-SU2 equivalence test in the complete isotypic
decomposition. Only the matching multiplicity representation remains, with
its full commuting group action preserved. -/
namespace Math.SU2IsotypicMatching
set_option autoImplicit false
noncomputable section
open Representation SU2FiniteBranching SU2IsotypicEvaluation ExternalInvariantTensor

theorem model_equiv_iff (a b : ℕ) :
    Nonempty (Representation.Equiv (model a) (model b)) ↔ a=b := by
  constructor
  · rintro ⟨e⟩
    have h := e.finrank_eq
    simp only [finrank_euclideanSpace_fin] at h
    omega
  · rintro rfl
    exact ⟨.refl _⟩

def zeroModelEquiv : Representation.Equiv (model 0) (Representation.trivial ℂ TauCeti.SU2 ℂ) :=
  (TauCeti.SU2.symPowerModelEquiv 0).symm.trans
    (by
      rw [← WeakDoubletScalars.symmetricPower_eq]
      exact SymmetricPowerLowDegree.representationZeroEquiv WeakDoubletScalars.doublet)

def zeroFactor {K B : Type*} [Group K] [AddCommGroup B] [Module ℂ B]
    (b : Representation ℂ K B) : Representation.Equiv
      (external (model 0) b) (b.comp (MonoidHom.snd TauCeti.SU2 K)) :=
  (externalEquiv zeroModelEquiv (Representation.Equiv.refl b)).trans
    { toLinearEquiv := TensorProduct.lid ℂ B
      isIntertwining' g := by
        apply TensorProduct.ext'
        intro z v
        change z • b g.2 v = b g.2 (z • v)
        exact (map_smul (b g.2) z v).symm }

local instance modelIrreducible (m : ℕ) : IsIrreducible (model m) :=
  TauCeti.SU2.isIrreducible_symPowerModel m

variable {K V B : Type*} [Group K] [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]
  (tau : Representation ℂ (TauCeti.SU2 × K) V) (N : ℕ)
  (C : Certificate (ProductFactorization.firstRestriction tau) N)
  (hr : ContinuousRepresentationScope.IsJointlyContinuous (ProductFactorization.firstRestriction tau))
  (b : Representation ℂ K B)

include C hr in
theorem hom_allowed_iff (m : Fin (N+1)) :
    SelectionCriteria.Allowed (IntertwiningMap tau (external (model m.val) b)) ↔
      SelectionCriteria.Allowed (IntertwiningMap (SU2IsotypicModels.action tau m.val) b) := by
  let e := SU2IsotypicModels.equivalence tau N C hr
  have ht := SelectionCriteria.allowed_equiv
    (CompactCoefficientSupport.homEquiv e.symm (Representation.Equiv.refl (external (model m.val) b)))
  refine ht.trans ((FiniteProductHomSupport.allowed_iff
    (SU2IsotypicModels.piece tau N) (external (model m.val) b)).trans ?_)
  have he (i : Fin (N+1)) :
      SelectionCriteria.Allowed (IntertwiningMap (SU2IsotypicModels.piece tau N i)
        (external (model m.val) b)) ↔
        i=m ∧ SelectionCriteria.Allowed (IntertwiningMap (SU2IsotypicModels.action tau i.val) b) := by
    have hi := ExternalIrreducibleMatch.hom_allowed_iff (model i.val) (model m.val)
      (SU2IsotypicModels.action tau i.val) b
    refine hi.trans (and_congr ?_ Iff.rfl)
    exact (model_equiv_iff i.val m.val).trans ⟨Fin.ext, fun h => congrArg Fin.val h⟩
  simp_rw [he]
  simp

/-- The bounded source supplies the complete certificate internally. -/
theorem ofBound [TopologicalSpace K]
    (ht : ContinuousRepresentationScope.IsJointlyContinuous tau)
    (hb : BoundedTorusWeights.Bounded (ProductFactorization.firstRestriction tau)
      TauCeti.SU2.torusHom N) (m : Fin (N+1)) :
    SelectionCriteria.Allowed (IntertwiningMap tau (external (model m.val) b)) ↔
      SelectionCriteria.Allowed (IntertwiningMap (SU2IsotypicModels.action tau m.val) b) :=
  hom_allowed_iff tau N
    (SU2FiniteBranching.exists_certificate _ _
      (ht.comp (ContinuousMonoidHom.inl TauCeti.SU2 K)) hb).some
    (ht.comp (ContinuousMonoidHom.inl TauCeti.SU2 K)) b m

end
end Math.SU2IsotypicMatching
