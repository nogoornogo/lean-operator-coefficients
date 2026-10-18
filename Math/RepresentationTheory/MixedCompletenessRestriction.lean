import Math.RepresentationTheory.MixedCoinvariantCompleteness
import Math.RepresentationTheory.InvariantHomRestriction

/-! Residual restriction commutes with intrinsic arbitrary-degree completeness. -/
namespace Math.MixedCompletenessRestriction
set_option autoImplicit false
noncomputable section
open Representation
variable {G H J A B : Type*} [Group G] [Group H] [Group J]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ G A) (b : Representation ℂ G B)
  (c : Representation ℂ H A) (d : Representation ℂ H B)
  (ha : ∀ g h v, a g (c h v) = c h (a g v))
  (hb : ∀ g h w, b g (d h w) = d h (b g w))
  (j : J →* H) (n m : ℕ)

@[reducible] local instance : AddCommGroup (MixedPowerDescent.Domain (A := A) (B := B) n m) :=
  inferInstance

abbrev Source := MixedCoinvariantCompleteness.Input a b c d ha hb n m
abbrev Target := MixedCoinvariantCompleteness.Input a b (c.comp j) (d.comp j)
  (fun g h v => ha g (j h) v) (fun g h w => hb g (j h) w) n m

def inputMap : Source a b c d ha hb n m →ₗ[ℂ] Target a b c d ha hb j n m where
  toFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' gh := f.isIntertwining' (gh.1,j gh.2) }
  map_add' _ _ := IntertwiningMap.ext rfl
  map_smul' _ _ := IntertwiningMap.ext rfl

theorem injective : Function.Injective (inputMap a b c d ha hb j n m) := by
  intro f g h
  apply IntertwiningMap.ext
  exact congrArg (fun f => f.toLinearMap) h

def residualMap : IntertwiningMap (MixedCoinvariantCompleteness.quotient a b c d ha hb n m)
    (trivial ℂ H ℂ) →ₗ[ℂ]
    IntertwiningMap (MixedCoinvariantCompleteness.quotient a b (c.comp j) (d.comp j)
      (fun g h v => ha g (j h) v) (fun g h w => hb g (j h) w) n m) (trivial ℂ J ℂ) where
  toFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' h := f.isIntertwining' (j h) }
  map_add' _ _ := IntertwiningMap.ext rfl
  map_smul' _ _ := IntertwiningMap.ext rfl

theorem extraction (f : Source a b c d ha hb n m) :
    MixedCoinvariantCompleteness.equiv a b (c.comp j) (d.comp j)
      (fun g h v => ha g (j h) v) (fun g h w => hb g (j h) w) n m
      (inputMap a b c d ha hb j n m f) =
    residualMap a b c d ha hb j n m (MixedCoinvariantCompleteness.equiv a b c d ha hb n m f) := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨u,rfl⟩ := (LocalCoinvariantHom.relations
    (MixedCoinvariantCompleteness.localAction a b n m)).mkQ_surjective u
  rfl

theorem reconstruction (f : IntertwiningMap
    (MixedCoinvariantCompleteness.quotient a b c d ha hb n m) (trivial ℂ H ℂ)) :
    (MixedCoinvariantCompleteness.equiv a b (c.comp j) (d.comp j)
      (fun g h v => ha g (j h) v) (fun g h w => hb g (j h) w) n m).symm
      (residualMap a b c d ha hb j n m f) =
    inputMap a b c d ha hb j n m ((MixedCoinvariantCompleteness.equiv a b c d ha hb n m).symm f) := by
  apply IntertwiningMap.ext
  rfl

theorem nonzero (h : ∃ f : Source a b c d ha hb n m, f ≠ 0) :
    ∃ f : Target a b c d ha hb j n m, f ≠ 0 := by
  obtain ⟨f,hf⟩ := h
  exact ⟨inputMap a b c d ha hb j n m f,
    fun hz => hf ((injective a b c d ha hb j n m)
      (hz.trans (inputMap a b c d ha hb j n m).map_zero.symm))⟩

theorem forbidden (h : ∀ f : Target a b c d ha hb j n m, f = 0) :
    ∀ f : Source a b c d ha hb n m, f = 0 := by
  intro f
  exact (injective a b c d ha hb j n m)
    ((h _).trans (inputMap a b c d ha hb j n m).map_zero.symm)

def surjectiveEquiv (hj : Function.Surjective j) :
    Source a b c d ha hb n m ≃ₗ[ℂ] Target a b c d ha hb j n m where
  toFun := inputMap a b c d ha hb j n m
  invFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' gh := by
      obtain ⟨h,hh⟩ := hj gh.2
      rcases gh with ⟨g,h'⟩
      dsimp at hh
      subst h'
      exact f.isIntertwining' (g,h) }
  left_inv _ := IntertwiningMap.ext rfl
  right_inv _ := IntertwiningMap.ext rfl
  map_add' := (inputMap a b c d ha hb j n m).map_add
  map_smul' := (inputMap a b c d ha hb j n m).map_smul
end
end Math.MixedCompletenessRestriction
