import Physics.FieldTheory.Mass.PhysicalSpeciesCopySurplus
import Math.RepresentationTheory.ProtectionConstraintPullback

/-! Physical exterior prohibition forces failure of a common three-species surplus. -/
namespace GUT.SpeciesSurplusNecessity
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor InvariantWeylMass
open PhysicalSpeciesCopySurplus Math.SelectionCriteria
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

variable {B : SymmetricMass rho}
  (X : Realization (aq := aq) (cq := cq) (au := au) (cu := cu) (ae := ae) (ce := ce) B)
  {R : Type*} [AddCommGroup R] [Module ℂ R] [FiniteDimensional ℂ R]

/-- This is the actual participating physical exterior domain, not a raw tensor. -/
abbrev ForbiddenExterior : Prop := Forbidden
  (QqueSpinorExterior.ExteriorCoefficient X.q.rangeRho X.u.rangeRho.dual X.e.rangeRho.dual)

theorem no_joint_surplus (r : Representation ℂ H R) [IsIrreducible r]
    (hq : IsSemisimpleRepresentation aq) (hu : IsSemisimpleRepresentation au)
    (he : IsSemisimpleRepresentation ae) (hf : ForbiddenExterior X) :
    ¬ (SpeciesCopySurplus.Surplus r aq cq ∧
      SpeciesCopySurplus.Surplus r au cu ∧ SpeciesCopySurplus.Surplus r ae ce) := by
  rintro ⟨dq,du,de⟩
  obtain ⟨f,hfne⟩ := (X.light_exterior r hq hu he dq du de).2.2.2
  exact hfne (hf f)

/-- For every common irreducible, at least one source Hom multiplicity cannot exceed its target. -/
theorem bottleneck (r : Representation ℂ H R) [IsIrreducible r]
    (hq : IsSemisimpleRepresentation aq) (hu : IsSemisimpleRepresentation au)
    (he : IsSemisimpleRepresentation ae) (hf : ForbiddenExterior X) :
    Module.finrank ℂ (IntertwiningMap r aq) ≤ Module.finrank ℂ (IntertwiningMap r cq) ∨
    Module.finrank ℂ (IntertwiningMap r au) ≤ Module.finrank ℂ (IntertwiningMap r cu) ∨
    Module.finrank ℂ (IntertwiningMap r ae) ≤ Module.finrank ℂ (IntertwiningMap r ce) := by
  have hn := no_joint_surplus X r hq hu he hf
  unfold SpeciesCopySurplus.Surplus at hn
  omega

/-- Symbolic copy parameters must be certified as the actual Hom multiplicities. -/
theorem count_bottleneck (r : Representation ℂ H R) [IsIrreducible r]
    (hq : IsSemisimpleRepresentation aq) (hu : IsSemisimpleRepresentation au)
    (he : IsSemisimpleRepresentation ae) (hf : ForbiddenExterior X)
    (sq tq su tu se te : ℕ)
    (hsq : Module.finrank ℂ (IntertwiningMap r aq) = sq)
    (htq : Module.finrank ℂ (IntertwiningMap r cq) = tq)
    (hsu : Module.finrank ℂ (IntertwiningMap r au) = su)
    (htu : Module.finrank ℂ (IntertwiningMap r cu) = tu)
    (hse : Module.finrank ℂ (IntertwiningMap r ae) = se)
    (hte : Module.finrank ℂ (IntertwiningMap r ce) = te) :
    sq ≤ tq ∨ su ≤ tu ∨ se ≤ te := by
  simpa only [hsq,htq,hsu,htu,hse,hte] using bottleneck X r hq hu he hf

/-- The resulting numeric predicate can be pulled back to any parameter family.
The supplied certificate must come from the physical theorem for that family. -/
theorem count_parameter_retain {I : Type*}
    (sm applicable prohibition : I → Prop)
    (sq tq su tu se te : I → ℕ)
    (physicalCertificate : ∀ i, applicable i → prohibition i →
      sq i ≤ tq i ∨ su i ≤ tu i ∨ se i ≤ te i)
    (i : I) (hs : sm i) (hp : prohibition i) :
    ProtectionConstraintPullback.retain sm applicable
      (fun i => sq i ≤ tq i ∨ su i ≤ tu i ∨ se i ≤ te i) i :=
  ProtectionConstraintPullback.preserve sm applicable prohibition _ physicalCertificate i hs hp

end
end GUT.SpeciesSurplusNecessity
