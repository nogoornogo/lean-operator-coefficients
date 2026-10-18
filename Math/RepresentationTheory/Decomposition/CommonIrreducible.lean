import Math.RepresentationTheory.Decomposition.SemisimpleSplitting

/-! Common irreducible constituents, expressed as isomorphic simple submodules
of the group-algebra modules attached to the two representations. -/
namespace Math.CommonIrreducible
noncomputable section
open Representation
open scoped MonoidAlgebra

variable {H V W : Type*} [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (rho : Representation ℂ H V) (sigma : Representation ℂ H W)

/-- Both constituents are actual submodules, not merely virtual characters. -/
def Shares : Prop :=
  ∃ S : Submodule ℂ[H] rho.asModule, ∃ T : Submodule ℂ[H] sigma.asModule,
    IsSimpleModule ℂ[H] S ∧ Nonempty (S ≃ₗ[ℂ[H]] T)

theorem nonzero_iff (hr : IsSemisimpleRepresentation rho) :
    (∃ f : IntertwiningMap rho sigma, f ≠ 0) ↔ Shares rho sigma := by
  let : IsSemisimpleModule ℂ[H] rho.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule rho).mp hr
  let e := IntertwiningMap.equivLinearMapAsModule rho sigma
  constructor
  · rintro ⟨f, hf⟩
    have hn : e f ≠ 0 := by
      intro hz
      exact hf (e.injective (hz.trans (map_zero e).symm))
    obtain ⟨S, hS, hne⟩ := LinearMap.exists_ne_zero_of_sSup_eq_top hn _
      (IsSemisimpleModule.sSup_simples_eq_top ℂ[H] rho.asModule)
    let : IsSimpleModule ℂ[H] S := hS
    let g := (e f).comp S.subtype
    have hg : Function.Injective g := LinearMap.injective_of_ne_zero hne
    exact ⟨S, g.range, hS, ⟨LinearEquiv.ofInjective g hg⟩⟩
  · rintro ⟨S, T, hS, ⟨st⟩⟩
    let : IsSimpleModule ℂ[H] S := hS
    let : Nontrivial S := IsSimpleModule.nontrivial ℂ[H] S
    obtain ⟨p, hp⟩ := IsSemisimpleModule.extension_property S.subtype S.subtype_injective
      (LinearMap.id : S →ₗ[ℂ[H]] S)
    let g := T.subtype.comp (st.toLinearMap.comp p)
    refine ⟨e.symm g, ?_⟩
    intro hz
    have hg : g = 0 := by
      have := congrArg e hz
      simpa using this
    obtain ⟨x, hx⟩ := exists_ne (0 : S)
    have he : g x.val = (st x).val := by
      change (st (p (S.subtype x))).val = (st x).val
      have hpx : p (S.subtype x) = x := LinearMap.congr_fun hp x
      rw [hpx]
    have hzero : st x = 0 := Subtype.ext (by simpa [hg] using he.symm)
    exact hx (st.injective (hzero.trans (map_zero st).symm))

theorem all_zero_iff (hr : IsSemisimpleRepresentation rho) :
    (∀ f : IntertwiningMap rho sigma, f = 0) ↔ ¬ Shares rho sigma := by
  simpa only [not_exists, not_not] using not_congr (nonzero_iff rho sigma hr)

end
end Math.CommonIrreducible
