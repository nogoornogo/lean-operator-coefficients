import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection
import Math.RepresentationTheory.Multiplicity.UnitaryMultiplicity

/-! # Split projections without finite-group Maschke assumptions -/

namespace Math.SemisimpleSplitting

noncomputable section

open Representation SplitRepresentationProjection
open scoped MonoidAlgebra

variable {H V W : Type*} [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Only the source representation needs to be semisimple, not the group algebra. -/
theorem exists_split (rho : Representation ℂ H V) (sigma : Representation ℂ H W)
    (hr : IsSemisimpleRepresentation rho)
    (p : IntertwiningMap rho sigma) (hp : Function.Surjective p) :
    ∃ S : Split rho sigma, S.project = p := by
  let : IsSemisimpleModule ℂ[H] rho.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule rho).mp hr
  let f := IntertwiningMap.equivLinearMapAsModule rho sigma p
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property f hp
    (LinearMap.id : sigma.asModule →ₗ[ℂ[H]] sigma.asModule)
  let e := (IntertwiningMap.equivLinearMapAsModule sigma rho).symm s
  refine ⟨⟨p, e, ?_⟩, rfl⟩
  intro x
  exact LinearMap.congr_fun hs x

/-- An injective intertwiner into a semisimple representation has an
equivariant retraction, with the original inclusion unchanged. -/
theorem exists_retraction (rho : Representation ℂ H V) (sigma : Representation ℂ H W)
    (hr : IsSemisimpleRepresentation rho)
    (i : IntertwiningMap sigma rho) (hi : Function.Injective i) :
    ∃ S : Split rho sigma, S.embed = i := by
  let : IsSemisimpleModule ℂ[H] rho.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule rho).mp hr
  let f := IntertwiningMap.equivLinearMapAsModule sigma rho i
  obtain ⟨p, hp⟩ := IsSemisimpleModule.extension_property f hi
    (LinearMap.id : sigma.asModule →ₗ[ℂ[H]] sigma.asModule)
  let q := (IntertwiningMap.equivLinearMapAsModule rho sigma).symm p
  refine ⟨⟨q, i, ?_⟩, rfl⟩
  intro x
  exact LinearMap.congr_fun hp x

end

/-- An existing unitary action supplies splitting for any group, including
infinite compact groups. Continuity is not needed for this algebraic step. -/
theorem exists_split_of_unitary {H V W : Type*} [Group H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (rho : Representation ℂ H V) (sigma : Representation ℂ H W)
    (hr : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (p : Representation.IntertwiningMap rho sigma) (hp : Function.Surjective p) :
    ∃ S : SplitRepresentationProjection.Split rho sigma, S.project = p :=
  exists_split rho sigma (UnitaryMultiplicity.isSemisimpleRepresentation_of_unitary rho hr) p hp

end Math.SemisimpleSplitting
