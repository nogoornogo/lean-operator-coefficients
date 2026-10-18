import Math.RepresentationTheory.SU2IsotypicEvaluation
import Math.RepresentationTheory.SubrepresentationTorusBound

/-! Continuous finite models of canonical SU2 multiplicities. Evaluation at
one nonzero vector realizes the entire multiplicity as an invariant range,
so the construction can be iterated for commuting spin/color factors. -/
namespace Math.SU2IsotypicModels
set_option autoImplicit false
noncomputable section
open Representation ProductFactorization SU2FiniteBranching SU2IsotypicEvaluation
open ContinuousRepresentationScope
open scoped TensorProduct

def seed (m : ℕ) : EuclideanSpace ℂ (Fin (m+1)) := EuclideanSpace.single 0 1

theorem seed_ne_zero (m : ℕ) : seed m ≠ 0 := by
  intro h
  have he := congrArg (fun x : EuclideanSpace ℂ (Fin (m+1)) => x 0) h
  simp [seed] at he

local instance modelIrreducible (m : ℕ) : IsIrreducible (model m) :=
  TauCeti.SU2.isIrreducible_symPowerModel m

variable {K V : Type*} [Group K] [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] (tau : Representation ℂ (TauCeti.SU2 × K) V)

abbrev Carrier (m : ℕ) : Type _ := ↥(MultiplicityRangeSpace tau (model m) (seed m))
abbrev action (m : ℕ) := multiplicityRangeRepresentation tau (model m) (seed m)

def multiplicityEquiv (m : ℕ) : Representation.Equiv
    (multiplicityRepresentation tau (model m)) (action tau m) :=
  multiplicityRangeEquiv tau (model m) (seed_ne_zero m)

variable (N : ℕ)
abbrev piece (m : Fin (N+1)) := ExternalTensorProduct.externalTprod (model m.val) (action tau m.val)

def pieceEquiv (m : Fin (N+1)) : Representation.Equiv
    (SU2IsotypicEvaluation.piece tau N m) (piece tau N m) where
  toLinearEquiv := TensorProduct.congr (.refl ℂ _) (multiplicityEquiv tau m.val).toLinearEquiv
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x f
    exact congrArg (fun y => model m.val g.1 x ⊗ₜ[ℂ] y)
      ((multiplicityEquiv tau m.val).toIntertwiningMap.isIntertwining _ _ g.2 f)

def piEquiv : Representation.Equiv
    (FiniteBlockHom.action (SU2IsotypicEvaluation.piece tau N))
    (FiniteBlockHom.action (piece tau N)) where
  toLinearEquiv := LinearEquiv.piCongrRight (fun m => (pieceEquiv tau N m).toLinearEquiv)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext m
    exact (pieceEquiv tau N m).toIntertwiningMap.isIntertwining _ _ g (x m)

def equivalence (C : Certificate (firstRestriction tau) N)
    (hr : IsJointlyContinuous (firstRestriction tau)) :
    Representation.Equiv (FiniteBlockHom.action (piece tau N)) tau :=
  (piEquiv tau N).symm.trans (SU2IsotypicEvaluation.equivalence tau N C hr)

variable [TopologicalSpace K]

omit [FiniteDimensional ℂ V] in
theorem continuous_action (m : ℕ) (hr : IsJointlyContinuous tau) :
    IsJointlyContinuous (action tau m) :=
  (hr.comp (ContinuousMonoidHom.inr TauCeti.SU2 K)).subrepresentation
    (multiplicityRange tau (model m) (seed m))

theorem inherit_bound [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (m : ℕ) (hr : IsJointlyContinuous tau)
    (t : Circle →* K) (B : ℕ)
    (hb : BoundedTorusWeights.Bounded (secondRestriction tau) t B) :
    BoundedTorusWeights.Bounded (action tau m) t B :=
  SubrepresentationTorusBound.subrepresentation (multiplicityRange tau (model m) (seed m))
    (CompactIrreducibleQuotient.semisimple (secondRestriction tau)
      (hr.comp (ContinuousMonoidHom.inr TauCeti.SU2 K))) t B hb

/-- Completeness with no supplied branching certificate: only the proved
bounded first-factor action is needed, and every K action is retained. -/
def ofBound (hr : IsJointlyContinuous tau)
    (hb : BoundedTorusWeights.Bounded (firstRestriction tau) TauCeti.SU2.torusHom N) :
    Representation.Equiv (FiniteBlockHom.action (piece tau N)) tau :=
  equivalence tau N
    (SU2FiniteBranching.exists_certificate _ _
      (hr.comp (ContinuousMonoidHom.inl TauCeti.SU2 K)) hb).some
    (hr.comp (ContinuousMonoidHom.inl TauCeti.SU2 K))

/-- Iteration through a multiplicity range needs no new weight bound premise.
The finite ambient dimension supplies a symbolic bound until sharpened. -/
def ofContinuous (hr : IsJointlyContinuous tau) :
    Representation.Equiv (FiniteBlockHom.action (piece tau (Module.finrank ℂ V))) tau :=
  equivalence tau (Module.finrank ℂ V)
    (SU2FiniteBranching.exists_certificate_of_dimension (firstRestriction tau)
      (hr.comp (ContinuousMonoidHom.inl TauCeti.SU2 K))).some
    (hr.comp (ContinuousMonoidHom.inl TauCeti.SU2 K))

end
end Math.SU2IsotypicModels
