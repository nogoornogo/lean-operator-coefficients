import Math.RepresentationTheory.BoundedTorusWeights
import Math.RepresentationTheory.Decomposition.SemisimpleSplitting

/-! Torus bounds survive equivariant transport and semisimple subobjects.
All maps and carriers stay abstract during restriction. -/
namespace Math.SubrepresentationTorusBound
set_option autoImplicit false
noncomputable section
open Representation BoundedTorusWeights
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {rho : Representation ℂ G V} {sigma : Representation ℂ G W}

theorem alongEquiv (e : Representation.Equiv rho sigma) (t : Circle →* G)
    (N : ℕ) (h : Bounded rho t N) : Bounded sigma t N :=
  bounded_of_surjective rho t sigma e.toIntertwiningMap e.surjective N h

theorem of_injective (f : IntertwiningMap sigma rho) (hf : Function.Injective f)
    (hr : IsSemisimpleRepresentation rho) (t : Circle →* G) (N : ℕ)
    (hb : Bounded rho t N) : Bounded sigma t N := by
  obtain ⟨S,_⟩ := SemisimpleSplitting.exists_retraction rho sigma hr f hf
  exact bounded_of_surjective rho t sigma S.project
    (fun x => ⟨S.embed x, S.left_inv x⟩) N hb

theorem subrepresentation (S : Subrepresentation rho)
    (hr : IsSemisimpleRepresentation rho) (t : Circle →* G) (N : ℕ)
    (hb : Bounded rho t N) : Bounded S.toRepresentation t N :=
  of_injective S.subtype S.toSubmodule.subtype_injective hr t N hb

end
end Math.SubrepresentationTorusBound
