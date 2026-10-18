import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.DFinsupp

/-! Algebraic common-kernel support, with semisimple source only. -/
namespace Math.AlgebraicCommonKernel
noncomputable section
open scoped BigOperators
variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

abbrev Components := isotypicComponents R M

def simple (c : Components (R := R) (M := M)) : Submodule R M := c.property.choose

theorem simple_spec (c : Components (R := R) (M := M)) :
    IsSimpleModule R (simple c) ∧ c.val = isotypicComponent R M (simple c) :=
  c.property.choose_spec

instance simpleInstance (c : Components (R := R) (M := M)) : IsSimpleModule R (simple c) :=
  (simple_spec c).1

def targetComponent (c : Components (R := R) (M := M)) : Submodule R N :=
  isotypicComponent R N (simple c)

def simpleInclusion (c : Components (R := R) (M := M)) : simple c →ₗ[R] c.val :=
  Submodule.inclusion (by rw [(simple_spec c).2]; exact Submodule.le_isotypicComponent _)

/-- If each source isotypic component injects by one of the available maps,
their images assemble to an injection of the whole semisimple source. -/
theorem assemble_injective [IsSemisimpleModule R M]
    (f : Components (R := R) (M := M) → M →ₗ[R] N)
    (hf : ∀ c, Function.Injective ((f c).comp c.val.subtype)) :
    ∃ F : M →ₗ[R] N, Function.Injective F := by
  classical
  have hi : ∀ c, Function.Injective ((f c).comp c.val.subtype |>.comp (simpleInclusion c)) :=
    fun c => (hf c).comp (Submodule.inclusion_injective _)
  let g (c : Components (R := R) (M := M)) := ((f c).comp c.val.subtype).comp (simpleInclusion c)
  let e c := LinearEquiv.ofInjective (g c) (hi c)
  have htc (c : Components (R := R) (M := M)) : targetComponent (N := N) c ∈ isotypicComponents R N := by
    refine ⟨(g c).range, IsSimpleModule.congr (e c).symm, ?_⟩
    exact (e c).isotypicComponent_eq (M := N)
  have htinj : Function.Injective (fun c : Components (R := R) (M := M) =>
      (⟨targetComponent (N := N) c, htc c⟩ : isotypicComponents R N)) := by
    intro c d he
    have hc : (g c).range ≤ targetComponent (N := N) d := by
      have hcd := congrArg Subtype.val he
      change targetComponent (N := N) c = targetComponent (N := N) d at hcd
      rw [← hcd]
      rintro _ ⟨v,rfl⟩
      exact (LinearMap.le_comap_isotypicComponent (simple c) (g c))
        (by rw [(isotypicComponent_eq_top_iff (R := R) (M := simple c)).mpr
          (IsIsotypicOfType.of_isSimpleModule R (simple c))]; exact Submodule.mem_top)
    let : IsSimpleModule R (g c).range := IsSimpleModule.congr (e c).symm
    have htype : Nonempty ((g c).range ≃ₗ[R] simple d) :=
      isIsotypicOfType_submodule_iff.mp
        (IsIsotypicOfType.isotypicComponent R N (simple d)) (g c).range hc
    obtain ⟨ed⟩ := htype
    apply Subtype.ext
    rw [(simple_spec c).2, (simple_spec d).2]
    exact ((e c).trans ed).isotypicComponent_eq
  have hind : iSupIndep (fun c : Components (R := R) (M := M) => targetComponent (N := N) c) :=
    ((sSupIndep_iff _).mp (sSupIndep_isotypicComponents R N)).comp htinj
  let fc (c : Components (R := R) (M := M)) : c.val →ₗ[R] targetComponent (N := N) c :=
    LinearMap.codRestrict _ ((f c).comp c.val.subtype) (fun x =>
      (LinearMap.le_comap_isotypicComponent (simple c) (f c))
        (by rw [← (simple_spec c).2]; exact x.property))
  have hfc c : Function.Injective (fc c) := by
    intro x y he
    exact hf c (congrArg Subtype.val he)
  let q := DFinsupp.mapRange.linearMap fc
  have hq : Function.Injective q := by
    intro x y he
    ext c
    exact congrArg Subtype.val (hfc c (congrArg (fun z => z c) he))
  let ind := (sSupIndep_iff _).mp (sSupIndep_isotypicComponents R M)
  have htop : (⨆ c : Components (R := R) (M := M), c.val) = ⊤ := by
    rw [← sSup_eq_iSup', sSup_isotypicComponents]
  let E := ind.linearEquiv htop
  let F := (DFinsupp.lsum ℕ (fun c => (targetComponent (N := N) c).subtype)).comp
    (q.comp E.symm.toLinearMap)
  exact ⟨F, hind.dfinsupp_lsum_injective.comp (hq.comp E.symm.injective)⟩


section Dimension
variable {k : Type*} [Field k] [Algebra k R]
  [Module k M] [IsScalarTower k R M] [FiniteDimensional k M]
  [Module k N] [IsScalarTower k R N] [FiniteDimensional k N]
  [IsSemisimpleModule R M]

omit [FiniteDimensional k M] in
theorem exists_uninjective_component {J : Type*} [Nonempty J]
    (f : J → M →ₗ[R] N) (hd : Module.finrank k N < Module.finrank k M) :
    ∃ c : Components (R := R) (M := M),
      ∀ j, ¬ Function.Injective ((f j).comp c.val.subtype) := by
  classical
  by_contra hn
  push Not at hn
  choose j hj using hn
  obtain ⟨F,hF⟩ := assemble_injective (fun c => f (j c)) hj
  have hle := LinearMap.finrank_le_finrank_of_injective (f := F.restrictScalars k) hF
  omega

omit [FiniteDimensional k M] in
/-- One source simple type occurs as an actual simple submodule in every
kernel. Target semisimplicity and topology are absent. -/
theorem exists_common_simple_kernel {J : Type*} [Nonempty J]
    (f : J → M →ₗ[R] N) (hd : Module.finrank k N < Module.finrank k M) :
    ∃ c : Components (R := R) (M := M), ∀ j,
      ∃ P : Submodule R M, P ≤ (f j).ker ∧ IsSimpleModule R P ∧
        Nonempty (P ≃ₗ[R] simple c) := by
  classical
  obtain ⟨c,hc⟩ := exists_uninjective_component f hd
  refine ⟨c, fun j => ?_⟩
  let K := ((f j).comp c.val.subtype).ker
  have hn : K ≠ ⊥ := by
    intro hz
    exact hc j (LinearMap.ker_eq_bot.mp hz)
  obtain ⟨L,hL,hSimple⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le K).resolve_left hn
  let : IsSimpleModule R L := hSimple
  have htype : IsIsotypicOfType R c.val (simple c) := by
    rw [(simple_spec c).2]
    exact IsIsotypicOfType.isotypicComponent R M (simple c)
  obtain ⟨e⟩ := htype L
  let P := L.map c.val.subtype
  let eP := L.equivMapOfInjective c.val.subtype c.val.subtype_injective
  refine ⟨P, ?_, IsSimpleModule.congr eP.symm, ⟨eP.symm.trans e⟩⟩
  exact Submodule.map_le_iff_le_comap.mpr hL

end Dimension

end
end Math.AlgebraicCommonKernel
