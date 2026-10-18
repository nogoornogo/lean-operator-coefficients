import Math.RepresentationTheory.MixedCoinvariantCompleteness
import Math.RepresentationTheory.LocalCoinvariantNaturality

/-! Arbitrary mixed-degree naturality, using directly induced mixed-power maps. -/
namespace Math.MixedCompletenessNaturality
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G H A B A' B' : Type*} [Group G] [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup A'] [Module ℂ A'] [AddCommGroup B'] [Module ℂ B']
  (a : Representation ℂ G A) (b : Representation ℂ G B)
  (c : Representation ℂ H A) (d : Representation ℂ H B)
  (ha : ∀ g h v, a g (c h v) = c h (a g v))
  (hb : ∀ g h w, b g (d h w) = d h (b g w))
  (a' : Representation ℂ G A') (b' : Representation ℂ G B')
  (c' : Representation ℂ H A') (d' : Representation ℂ H B')
  (ha' : ∀ g h v, a' g (c' h v) = c' h (a' g v))
  (hb' : ∀ g h w, b' g (d' h w) = d' h (b' g w))
  (f : IntertwiningMap c c') (t : IntertwiningMap d d')
  (hf : ∀ g v, f (a g v) = a' g (f v))
  (ht : ∀ g w, t (b g w) = b' g (t w))
  (n m : ℕ)

@[reducible] local instance : AddCommGroup (MixedPowerDescent.Domain (A := A) (B := B) n m) :=
  inferInstance
@[reducible] local instance : AddCommGroup (MixedPowerDescent.Domain (A := A') (B := B') n m) :=
  inferInstance

def mixedMap : IntertwiningMap (MixedCoinvariantCompleteness.residual c d n m)
    (MixedCoinvariantCompleteness.residual c' d' n m) :=
  (f.exteriorPower n).tensor (t.symmetricPower m)

@[simp] theorem mixedMap_pure (v : Fin n → A) (w : Fin m → B) :
    mixedMap c d c' d' f t n m (MixedWeightSupport.pure v w) =
      MixedWeightSupport.pure (f ∘ v) (t ∘ w) := by
  change TensorProduct.map (exteriorPower.map n f.toLinearMap)
    (SymmetricPower.map t.toLinearMap) (_ ⊗ₜ[ℂ] _) = _
  rw [TensorProduct.map_tmul, exteriorPower.map_apply_ιMulti, SymmetricPower.map_tprod]
  rfl

include hf ht in
theorem local_compatible (g : G) (u : MixedPowerDescent.Domain (A := A) (B := B) n m) :
    mixedMap c d c' d' f t n m (MixedCoinvariantCompleteness.localAction a b n m g u) =
      MixedCoinvariantCompleteness.localAction a' b' n m g (mixedMap c d c' d' f t n m u) := by
  have he : (mixedMap c d c' d' f t n m).toLinearMap.comp
      (MixedCoinvariantCompleteness.localAction a b n m g) =
      (MixedCoinvariantCompleteness.localAction a' b' n m g).comp
        (mixedMap c d c' d' f t n m).toLinearMap := by
    apply MixedPowerDescent.ext (A := A) (B := B)
      (N := MixedPowerDescent.Domain (A := A') (B := B') n m) n m
    intro v w
    change mixedMap c d c' d' f t n m
      ((MixedCoinvariantCompleteness.localAction a b n m g) (MixedWeightSupport.pure v w)) =
      (MixedCoinvariantCompleteness.localAction a' b' n m g)
        (mixedMap c d c' d' f t n m (MixedWeightSupport.pure v w))
    have act (r : Representation ℂ G A) (s : Representation ℂ G B) :
        MixedCoinvariantCompleteness.localAction r s n m g (MixedWeightSupport.pure v w) =
        MixedWeightSupport.pure (r g ∘ v) (s g ∘ w) := by
      simp only [MixedCoinvariantCompleteness.localAction, MixedWeightSupport.pure,
        Representation.tprod_apply, TensorProduct.map_tmul,
        Representation.exteriorPower_apply_ιMulti, Representation.symmetricPower_apply_tprod]
      rfl
    rw [act, mixedMap_pure, mixedMap_pure]
    simp only [MixedCoinvariantCompleteness.localAction, MixedWeightSupport.pure,
      Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.exteriorPower_apply_ιMulti, Representation.symmetricPower_apply_tprod,
      Function.comp_def, hf, ht]
  exact LinearMap.congr_fun he u


def quotientMap : IntertwiningMap (MixedCoinvariantCompleteness.quotient a b c d ha hb n m)
    (MixedCoinvariantCompleteness.quotient a' b' c' d' ha' hb' n m) :=
  LocalCoinvariantNaturality.quotientMap (k := ℂ) (G := G) (H := H)
    (U := MixedPowerDescent.Domain (A := A) (B := B) n m)
    (V := MixedPowerDescent.Domain (A := A') (B := B') n m)
    (MixedCoinvariantCompleteness.localAction a b n m)
    (MixedCoinvariantCompleteness.residual c d n m)
    (MixedCoinvariantCompleteness.commutes a b c d ha hb n m)
    (MixedCoinvariantCompleteness.localAction a' b' n m)
    (MixedCoinvariantCompleteness.residual c' d' n m)
    (MixedCoinvariantCompleteness.commutes a' b' c' d' ha' hb' n m)
    (mixedMap c d c' d' f t n m) (local_compatible a b c d a' b' c' d' f t hf ht n m)


def pull : MixedCoinvariantCompleteness.Input a' b' c' d' ha' hb' n m →ₗ[ℂ]
    MixedCoinvariantCompleteness.Input a b c d ha hb n m where
  toFun q := {
    toLinearMap := q.toLinearMap.comp (mixedMap c d c' d' f t n m).toLinearMap
    isIntertwining' gh := by
      apply LinearMap.ext
      intro u
      change q (mixedMap c d c' d' f t n m
        (MixedCoinvariantCompleteness.localAction a b n m gh.1
          (MixedCoinvariantCompleteness.residual c d n m gh.2 u))) =
        q (mixedMap c d c' d' f t n m u)
      rw [local_compatible a b c d a' b' c' d' f t hf ht n m,
        IntertwiningMap.isIntertwining]
      exact IntertwiningMap.isIntertwining _ _ q gh _ }
  map_add' _ _ := by ext u; rfl
  map_smul' _ _ := by ext u; rfl

theorem extraction (q : MixedCoinvariantCompleteness.Input a' b' c' d' ha' hb' n m) :
    MixedCoinvariantCompleteness.equiv a b c d ha hb n m
      (pull a b c d ha hb a' b' c' d' ha' hb' f t hf ht n m q) =
    (MixedCoinvariantCompleteness.equiv a' b' c' d' ha' hb' n m q).comp
      (quotientMap a b c d ha hb a' b' c' d' ha' hb' f t hf ht n m) := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨u,rfl⟩ := (LocalCoinvariantHom.relations
    (MixedCoinvariantCompleteness.localAction a b n m)).mkQ_surjective u
  rfl

theorem reconstruction
    (q : IntertwiningMap (MixedCoinvariantCompleteness.quotient a' b' c' d' ha' hb' n m)
      (trivial ℂ H ℂ)) :
    (MixedCoinvariantCompleteness.equiv a b c d ha hb n m).symm
      (q.comp (quotientMap a b c d ha hb a' b' c' d' ha' hb' f t hf ht n m)) =
    pull a b c d ha hb a' b' c' d' ha' hb' f t hf ht n m
      ((MixedCoinvariantCompleteness.equiv a' b' c' d' ha' hb' n m).symm q) := by
  apply IntertwiningMap.ext
  rfl
end
end Math.MixedCompletenessNaturality
