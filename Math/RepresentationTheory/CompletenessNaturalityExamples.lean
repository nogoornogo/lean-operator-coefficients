import Math.RepresentationTheory.InvariantHomRestriction
import Math.RepresentationTheory.FamilyStabilizer
import Math.RepresentationTheory.MixedCompletenessNaturality
import Math.RepresentationTheory.MixedCompletenessRestriction
import Mathlib.Tactic

/-! Exact controls: restriction is injective, not generally an equivalence. -/
namespace Math.CompletenessNaturalityExamples
set_option autoImplicit false
noncomputable section
open Representation

abbrev unitAction := trivial ℂ Unit ℂ

def doubling : IntertwiningMap unitAction unitAction where
  toLinearMap := (2 : ℂ) • LinearMap.id
  isIntertwining' _ := by apply LinearMap.ext; intro z; rfl

theorem mixed_one_two (v : Fin 1 → ℂ) (w : Fin 2 → ℂ) :
    MixedCompletenessNaturality.mixedMap unitAction unitAction unitAction unitAction
      doubling (IntertwiningMap.id unitAction) 1 2 (MixedWeightSupport.pure v w) =
    MixedWeightSupport.pure (fun i => 2 * v i) w := by
  rw [MixedCompletenessNaturality.mixedMap_pure]
  rfl

theorem unit_cover_surjective : Function.Surjective (MonoidHom.fst Unit Unit) := by
  intro u
  exact ⟨(u,()),rfl⟩

def unitCoverEquiv : InvariantHomRestriction.Space unitAction ≃ₗ[ℂ]
    InvariantHomRestriction.Space (unitAction.comp (MonoidHom.fst Unit Unit)) :=
  InvariantHomRestriction.surjectiveEquiv unitAction (MonoidHom.fst Unit Unit) unit_cover_surjective

def phaseAction : Representation ℂ ℂˣ ℂ where
  toFun u := (u : ℂ) • LinearMap.id
  map_one' := by apply LinearMap.ext; intro z; simp
  map_mul' u v := by apply LinearMap.ext; intro z; simp [mul_comm, mul_left_comm]

theorem phase_forbidden : ∀ f : InvariantHomRestriction.Space phaseAction, f = 0 := by
  intro f
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  have h := IntertwiningMap.isIntertwining _ _ f (-1) z
  have he' : f (-z) = f z := by simpa [phaseAction] using h
  have he : -(f z) = f z := by
    change -(f.toLinearMap z) = f.toLinearMap z
    rw [← map_neg]
    exact he'
  change f z = 0
  linear_combination (-1 / 2 : ℂ) * he

def trivialCoefficient : InvariantHomRestriction.Space
    (phaseAction.comp (⊥ : Subgroup ℂˣ).subtype) where
  toLinearMap := LinearMap.id
  isIntertwining' u := by
    have hu : (u : ℂˣ) = 1 := (Subgroup.mem_bot.mp u.property)
    apply LinearMap.ext
    intro z
    simp [phaseAction, hu]

theorem trivial_nonzero : trivialCoefficient ≠ 0 := by
  intro h
  have he := congrArg (fun f : InvariantHomRestriction.Space
    (phaseAction.comp (⊥ : Subgroup ℂˣ).subtype) => f 1) h
  exact one_ne_zero he

theorem restriction_not_surjective : ¬ Function.Surjective
    (InvariantHomRestriction.restrict phaseAction (⊥ : Subgroup ℂˣ).subtype) := by
  intro h
  obtain ⟨f,hf⟩ := h trivialCoefficient
  rw [phase_forbidden f, map_zero] at hf
  exact trivial_nonzero hf.symm

theorem extra_data_stabilizer_le {G V P Q : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] (a : Representation ℂ G V)
    (v : P → V) (w : Q → V) :
    FamilyStabilizer.subgroup a (Sum.elim v w) ≤ FamilyStabilizer.subgroup a v := by
  intro g hg p
  exact hg (.inl p)

theorem data_allowance {G V U P Q : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (a : Representation ℂ G V) (b : Representation ℂ G U) (v : P → V) (w : Q → V)
    (h : ∃ f : InvariantHomRestriction.Space (b.comp (FamilyStabilizer.subgroup a v).subtype), f ≠ 0) :
    ∃ f : InvariantHomRestriction.Space
      (b.comp (FamilyStabilizer.subgroup a (Sum.elim v w)).subtype), f ≠ 0 :=
  InvariantHomRestriction.subgroup_nonzero b _ _ (extra_data_stabilizer_le a v w) h
end
end Math.CompletenessNaturalityExamples
