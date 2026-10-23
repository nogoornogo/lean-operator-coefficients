import Physics.FieldTheory.Mass.Surplus.PhysicalCommonCopyModel
import Math.RepresentationTheory.Decomposition.SpeciesCopySurplus

/-! Independent species copy surpluses on an original invariant symmetric mass.
Light membership and the physical exterior coefficient are derived. -/
namespace Physics.PhysicalSpeciesCopySurplus
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor InvariantWeylMass ExternalInvariantTensor
open SplitRepresentationProjection PhysicalCommonCopyModel
open scoped MonoidAlgebra
variable {H F Aq Cq Au Cu Ae Ce : Type*} [Group H]
  [AddCommGroup F] [Module ℂ F]
  [AddCommGroup Aq] [Module ℂ Aq] [FiniteDimensional ℂ Aq]
  [AddCommGroup Cq] [Module ℂ Cq] [FiniteDimensional ℂ Cq]
  [AddCommGroup Au] [Module ℂ Au] [FiniteDimensional ℂ Au]
  [AddCommGroup Cu] [Module ℂ Cu] [FiniteDimensional ℂ Cu]
  [AddCommGroup Ae] [Module ℂ Ae] [FiniteDimensional ℂ Ae]
  [AddCommGroup Ce] [Module ℂ Ce] [FiniteDimensional ℂ Ce]
  {aq : Representation ℂ H Aq} {cq : Representation ℂ H Cq}
  {au : Representation ℂ H Au} {cu : Representation ℂ H Cu}
  {ae : Representation ℂ H Ae} {ce : Representation ℂ H Ce}
  {rho : Representation ℂ (GaugeGroup × H) F}

structure Realization (B : SymmetricMass rho) where
  q : Species (s := aq) (t := cq) quark B
  u : Species (s := au) (t := cu) upRight.dual B
  e : Species (s := ae) (t := ce) electronRight.dual B

namespace Realization
variable {B : SymmetricMass rho}
  (X : Realization (aq := aq) (cq := cq) (au := au) (cu := cu) (ae := ae) (ce := ce) B)

def quarkEq : Representation.Equiv X.q.rangeRho
    (QqueSpinorExterior.qField (a := X.q.map.ker.toRepresentation)) :=
  RepresentationConjugation.equiv _ _

def upEq : Representation.Equiv X.u.rangeRho.dual
    (QqueSpinorExterior.uField (b := X.u.map.ker.toRepresentation)) :=
  (dualEquiv (RepresentationConjugation.equiv _ _)).trans
    ((dualExternalEquiv upRight.dual X.u.map.ker.toRepresentation).symm.trans
      (externalEquiv (bidualEquiv upRight).symm (Representation.Equiv.refl _)))

def electronEq : Representation.Equiv X.e.rangeRho.dual
    (QqueSpinorExterior.eField (d := X.e.map.ker.toRepresentation)) :=
  (dualEquiv (RepresentationConjugation.equiv _ _)).trans
    ((dualExternalEquiv electronRight.dual X.e.map.ker.toRepresentation).symm.trans
      (externalEquiv (bidualEquiv electronRight).symm (Representation.Equiv.refl _)))

def HasLightExterior : Prop :=
  (∀ x : LinearMap.range X.q.lightEmbedding.toLinearMap, x.val ∈ B.radical.toSubmodule) ∧
  (∀ x : LinearMap.range X.u.lightEmbedding.toLinearMap, x.val ∈ B.radical.toSubmodule) ∧
  (∀ x : LinearMap.range X.e.lightEmbedding.toLinearMap, x.val ∈ B.radical.toSubmodule) ∧
  PhysicalQqueEndpoint.HasExterior X.q.rangeRho X.u.rangeRho.dual X.e.rangeRho.dual

variable {R : Type*} [AddCommGroup R] [Module ℂ R] [FiniteDimensional ℂ R]

theorem light_exterior (r : Representation ℂ H R) [IsIrreducible r]
    (hq : IsSemisimpleRepresentation aq) (hu : IsSemisimpleRepresentation au)
    (he : IsSemisimpleRepresentation ae)
    (dq : SpeciesCopySurplus.Surplus r aq cq)
    (du : SpeciesCopySurplus.Surplus r au cu)
    (de : SpeciesCopySurplus.Surplus r ae ce) : X.HasLightExterior := by
  let : Nontrivial R := IsSimpleModule.nontrivial ℂ[H] r.asModule
  obtain ⟨sq⟩ := SpeciesCopySurplus.exists_kernel_split r aq cq X.q.map hq dq
  obtain ⟨su⟩ := SpeciesCopySurplus.exists_kernel_split r au cu X.u.map hu du
  obtain ⟨se⟩ := SpeciesCopySurplus.exists_kernel_split r ae ce X.e.map he de
  refine ⟨X.q.range_light, X.u.range_light, X.e.range_light, ?_⟩
  apply PhysicalQqueEndpoint.of_alternation
  exact QqueSpinorExterior.exists_on_fields sq su se
    X.q.rangeRho X.u.rangeRho.dual X.e.rangeRho.dual X.quarkEq X.upEq X.electronEq
end Realization

structure Model (aq : Representation ℂ H Aq) (cq : Representation ℂ H Cq)
    (au : Representation ℂ H Au) (cu : Representation ℂ H Cu)
    (ae : Representation ℂ H Ae) (ce : Representation ℂ H Ce)
    (rho : Representation ℂ (GaugeGroup × H) F) where
  realize : (B : SymmetricMass rho) →
    Realization (aq := aq) (cq := cq) (au := au) (cu := cu) (ae := ae) (ce := ce) B

variable {R : Type*} [AddCommGroup R] [Module ℂ R] [FiniteDimensional ℂ R]
theorem Model.arbitrary_mass_light_exterior (X : Model aq cq au cu ae ce rho)
    (B : SymmetricMass rho) (r : Representation ℂ H R) [IsIrreducible r]
    (hq : IsSemisimpleRepresentation aq) (hu : IsSemisimpleRepresentation au)
    (he : IsSemisimpleRepresentation ae)
    (dq : SpeciesCopySurplus.Surplus r aq cq)
    (du : SpeciesCopySurplus.Surplus r au cu)
    (de : SpeciesCopySurplus.Surplus r ae ce) :
    (X.realize B).HasLightExterior :=
  (X.realize B).light_exterior r hq hu he dq du de

end
end Physics.PhysicalSpeciesCopySurplus
