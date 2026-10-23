import Math.RepresentationTheory.Constructions.CommutingActionHom
import Math.RepresentationTheory.Constructions.MixedPowerDescent
import Math.RepresentationTheory.Invariants.DirectSumFunctionalProduct

/-! Intrinsic arbitrary-degree completeness before the content-wise presentation.
Both coefficient input and residual quotient are independently constructed. -/
namespace Math.MixedCoinvariantCompleteness
set_option autoImplicit false
noncomputable section
open Representation
variable {G H A B : Type*} [Group G] [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ G A) (b : Representation ℂ G B)
  (c : Representation ℂ H A) (d : Representation ℂ H B)
  (ha : ∀ g h v, a g (c h v) = c h (a g v))
  (hb : ∀ g h w, b g (d h w) = d h (b g w))
  (n m : ℕ)

def localAction : Representation ℂ G (MixedPowerDescent.Domain (A := A) (B := B) n m) :=
  (a.exteriorPower n).tprod (b.symmetricPower m)
def residual : Representation ℂ H (MixedPowerDescent.Domain (A := A) (B := B) n m) :=
  (c.exteriorPower n).tprod (d.symmetricPower m)

include ha hb in
theorem commutes : ∀ g h u, localAction a b n m g (residual c d n m h u) =
    residual c d n m h (localAction a b n m g u) := by
  intro g h
  have he : (localAction a b n m g).comp (residual c d n m h) =
      (residual c d n m h).comp (localAction a b n m g) := by
    apply MixedPowerDescent.ext (A := A) (B := B)
      (N := MixedPowerDescent.Domain (A := A) (B := B) n m) n m
    intro v w
    simp only [localAction, residual, LinearMap.comp_apply, MixedWeightSupport.pure,
      Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.exteriorPower_apply_ιMulti, Representation.symmetricPower_apply_tprod,
      Function.comp_def, ha, hb]
  exact LinearMap.congr_fun he

abbrev Input := IntertwiningMap
  (CommutingActionHom.action (k := ℂ)
    (U := MixedPowerDescent.Domain (A := A) (B := B) n m)
    (localAction a b n m) (residual c d n m)
    (commutes a b c d ha hb n m)) ((trivial ℂ H ℂ).comp (MonoidHom.snd G H))

abbrev quotient :=
  LocalCoinvariantHom.quotient (k := ℂ)
    (U := MixedPowerDescent.Domain (A := A) (B := B) n m)
    (localAction a b n m) (residual c d n m)
  (commutes a b c d ha hb n m)

/-- Arbitrary mixed degrees, no local basis, compactness or finite flavor dimension. -/
def equiv : Input a b c d ha hb n m ≃ₗ[ℂ]
    IntertwiningMap (quotient a b c d ha hb n m) (trivial ℂ H ℂ) :=
  CommutingActionHom.equiv (k := ℂ)
    (U := MixedPowerDescent.Domain (A := A) (B := B) n m)
    (localAction a b n m) (residual c d n m) (trivial ℂ H ℂ)
    (commutes a b c d ha hb n m)

theorem extract_mk (f : Input a b c d ha hb n m)
    (u : MixedPowerDescent.Domain (A := A) (B := B) n m) :
    equiv a b c d ha hb n m f (Submodule.Quotient.mk u) = f u := rfl

theorem forbidden_iff : (∀ f : Input a b c d ha hb n m, f = 0) ↔
    ∀ f : IntertwiningMap (quotient a b c d ha hb n m) (trivial ℂ H ℂ), f = 0 := by
  constructor
  · intro h f
    have he := congrArg (equiv a b c d ha hb n m) (h ((equiv a b c d ha hb n m).symm f))
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using he
  · intro h f
    apply (equiv a b c d ha hb n m).injective
    simpa only [map_zero] using h ((equiv a b c d ha hb n m) f)

theorem nonzero_iff : (∃ f : Input a b c d ha hb n m, f ≠ 0) ↔
    ∃ f : IntertwiningMap (quotient a b c d ha hb n m) (trivial ℂ H ℂ), f ≠ 0 := by
  simpa only [not_forall, not_not] using not_congr (forbidden_iff a b c d ha hb n m)

/-- The algebraic dual of the all-degree carrier is a product, not a direct sum. -/
def allEquiv : (∀ z : ℕ × ℕ, Input a b c d ha hb z.1 z.2) ≃ₗ[ℂ]
    IntertwiningMap (Representation.directSum
      (fun z : ℕ × ℕ => quotient a b c d ha hb z.1 z.2)) (trivial ℂ H ℂ) :=
  (LinearEquiv.piCongrRight (fun z : ℕ × ℕ => equiv a b c d ha hb z.1 z.2)).trans
    (DirectSumFunctionalProduct.equiv
      (fun z : ℕ × ℕ => quotient a b c d ha hb z.1 z.2)).symm

theorem all_forbidden_iff :
    (∀ f : IntertwiningMap (Representation.directSum
      (fun z : ℕ × ℕ => quotient a b c d ha hb z.1 z.2)) (trivial ℂ H ℂ), f = 0) ↔
    ∀ n m, ∀ f : Input a b c d ha hb n m, f = 0 := by
  rw [DirectSumFunctionalProduct.forbidden_iff]
  constructor
  · intro h n m
    exact (forbidden_iff a b c d ha hb n m).mpr (h (n,m))
  · intro h z
    exact (forbidden_iff a b c d ha hb z.1 z.2).mp (h z.1 z.2)

theorem all_nonzero_iff :
    (∃ f : IntertwiningMap (Representation.directSum
      (fun z : ℕ × ℕ => quotient a b c d ha hb z.1 z.2)) (trivial ℂ H ℂ), f ≠ 0) ↔
    ∃ n m, ∃ f : Input a b c d ha hb n m, f ≠ 0 := by
  simpa only [not_forall, not_not] using not_congr (all_forbidden_iff a b c d ha hb)

end
end Math.MixedCoinvariantCompleteness
