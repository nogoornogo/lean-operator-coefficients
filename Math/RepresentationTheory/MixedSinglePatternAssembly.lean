import Math.RepresentationTheory.MixedSingleBosonDescent
import Math.RepresentationTheory.TypedPatternAlternation
import Math.RepresentationTheory.MixedSpeciesExt

/-! Normalized assembly of an ordered fermion pattern and one typed boson.
The construction starts from an invariant, exchange-compatible ordered map;
its canonical restriction recovers that map exactly. -/
namespace Math.MixedSinglePatternAssembly
set_option autoImplicit false
noncomputable section
open Representation FiniteSpeciesExterior
variable {P Q G : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] [Group G]
  {V : P → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {W : Q → Type*} [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  (r : ∀ s, Representation ℂ G (V s)) (t : ∀ s, Representation ℂ G (W s))
  {n : ℕ} (pattern : Fin n → P) (scalar : Q)

def spectatorLift : (W scalar →ₗ[ℂ] ℂ) →ₗ[ℂ] ((∀ s, W s) →ₗ[ℂ] ℂ) where
  toFun f := f.comp (LinearMap.proj scalar)
  map_add' f h := by ext w; rfl
  map_smul' z f := by ext w; rfl

def lifted (k : MultilinearMap ℂ (fun i => V (pattern i)) (W scalar →ₗ[ℂ] ℂ)) :=
  (spectatorLift scalar).compMultilinearMap k

def Invariant (k : MultilinearMap ℂ (fun i => V (pattern i)) (W scalar →ₗ[ℂ] ℂ)) : Prop :=
  ∀ g v w, k (fun i => r (pattern i) g (v i)) (t scalar g w) = k v w

omit [Fintype P] [DecidableEq P] in
theorem lifted_compatible (k : MultilinearMap ℂ (fun i => V (pattern i)) (W scalar →ₗ[ℂ] ℂ))
    (hk : TypedPatternAlternation.Compatible pattern k) :
    TypedPatternAlternation.Compatible pattern (lifted pattern scalar k) := by
  intro p hp v
  apply LinearMap.ext
  intro w
  exact LinearMap.congr_fun (hk p hp v) (w scalar)

def orderedExtension (k : MultilinearMap ℂ (fun i => V (pattern i)) (W scalar →ₗ[ℂ] ℂ)) :=
  TypedPatternAlternation.alternating pattern (lifted pattern scalar k)

theorem orderedExtension_invariant
    (k : MultilinearMap ℂ (fun i => V (pattern i)) (W scalar →ₗ[ℂ] ℂ))
    (hk : Invariant r t pattern scalar k) :
    ∀ g v w, orderedExtension pattern scalar k (representation r g ∘ v)
      (representation t g w) = orderedExtension pattern scalar k v w := by
  intro g v w
  simp only [orderedExtension, TypedPatternAlternation.alternating, AlternatingMap.smul_apply,
    LinearMap.smul_apply]
  congr 1
  simp only [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  change k (fun i => r (pattern i) g (v (p i) (pattern i)))
    (t scalar g (w scalar)) = k (fun i => v (p i) (pattern i)) (w scalar)
  exact hk g _ _

def assemble (k : MultilinearMap ℂ (fun i => V (pattern i)) (W scalar →ₗ[ℂ] ℂ))
    (hk : Invariant r t pattern scalar k) :
    MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := 1) :=
  MixedSingleBosonDescent.descend n (representation r) (representation t)
    ⟨orderedExtension pattern scalar k, orderedExtension_invariant r t pattern scalar k hk⟩

theorem restriction_assemble
    (k : MultilinearMap ℂ (fun i => V (pattern i)) (W scalar →ₗ[ℂ] ℂ))
    (hk : Invariant r t pattern scalar k) (hc : TypedPatternAlternation.Compatible pattern k)
    (v : ∀ i, V (pattern i)) (w : W scalar) :
    assemble r t pattern scalar k hk (MixedWeightSupport.pure
      (fun i => Pi.single (pattern i) (v i)) (fun _ : Fin 1 => Pi.single scalar w)) = k v w := by
  change (MixedSingleBosonDescent.orderedEquiv n).symm (orderedExtension pattern scalar k)
    (MixedWeightSupport.pure _ _) = _
  rw [MixedSingleBosonDescent.lift_apply]
  change (TypedPatternAlternation.alternating pattern (lifted pattern scalar k)
    (fun i => Pi.single (pattern i) (v i))) (Pi.single scalar w) = _
  rw [TypedPatternAlternation.alternating_pure pattern _ (lifted_compatible pattern scalar k hc)]
  simp [lifted, spectatorLift]

def spectatorRestrict : ((∀ s, W s) →ₗ[ℂ] ℂ) →ₗ[ℂ] (W scalar →ₗ[ℂ] ℂ) where
  toFun f := f.comp (LinearMap.single ℂ W scalar)
  map_add' f h := by ext w; rfl
  map_smul' z f := by ext w; rfl

def restriction
    (f : MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := 1)) :=
  (spectatorRestrict scalar).compMultilinearMap
    (((MixedSingleBosonDescent.extract n (representation r) (representation t) f).val.toMultilinearMap).compLinearMap
      (fun i => LinearMap.single ℂ V (pattern i)))

@[simp] theorem restriction_apply
    (f : MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := 1))
    (v : ∀ i, V (pattern i)) (w : W scalar) :
    restriction r t pattern scalar f v w =
      f (MixedWeightSupport.pure (fun i => Pi.single (pattern i) (v i))
        (fun _ : Fin 1 => Pi.single scalar w)) := rfl

theorem restriction_assemble_eq
    (k : MultilinearMap ℂ (fun i => V (pattern i)) (W scalar →ₗ[ℂ] ℂ))
    (hk : Invariant r t pattern scalar k) (hc : TypedPatternAlternation.Compatible pattern k) :
    restriction r t pattern scalar (assemble r t pattern scalar k hk) = k := by
  apply MultilinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  rw [restriction_apply, restriction_assemble r t pattern scalar k hk hc]

theorem assemble_vanish_fermions
    (k : MultilinearMap ℂ (fun i => V (pattern i)) (W scalar →ₗ[ℂ] ℂ))
    (hk : Invariant r t pattern scalar k)
    (labels : Fin n → P) (v : ∀ i, V (labels i)) (w : ∀ s, W s)
    (h : ¬ ∃ p : Equiv.Perm (Fin n), labels ∘ p = pattern) :
    assemble r t pattern scalar k hk (MixedWeightSupport.pure
      (fun i => Pi.single (labels i) (v i)) (fun _ : Fin 1 => w)) = 0 := by
  change (MixedSingleBosonDescent.orderedEquiv n).symm (orderedExtension pattern scalar k) _ = 0
  rw [MixedSingleBosonDescent.lift_apply]
  change (TypedPatternAlternation.alternating pattern (lifted pattern scalar k)
    (fun i => Pi.single (labels i) (v i))) w = 0
  rw [TypedPatternAlternation.alternating_vanish pattern _ labels v h]
  rfl

theorem assemble_vanish_scalar
    (k : MultilinearMap ℂ (fun i => V (pattern i)) (W scalar →ₗ[ℂ] ℂ))
    (hk : Invariant r t pattern scalar k) (v : Fin n → ∀ s, V s)
    (u : Q) (w : W u) (h : scalar ≠ u) :
    assemble r t pattern scalar k hk (MixedWeightSupport.pure v
      (fun _ : Fin 1 => Pi.single u w)) = 0 := by
  change (MixedSingleBosonDescent.orderedEquiv n).symm (orderedExtension pattern scalar k) _ = 0
  rw [MixedSingleBosonDescent.lift_apply]
  simp [orderedExtension, TypedPatternAlternation.alternating,
    MultilinearMap.alternatization_apply, TypedPatternAlternation.ordered,
    lifted, spectatorLift, Pi.single_eq_of_ne h]

theorem restriction_invariant
    (f : MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := 1)) :
    Invariant r t pattern scalar (restriction r t pattern scalar f) := by
  intro g v w
  have h := (MixedSingleBosonDescent.extract n (representation r) (representation t) f).property g
    (fun i => Pi.single (pattern i) (v i)) (Pi.single scalar w)
  have hr : representation r g ∘ (fun i => Pi.single (pattern i) (v i)) =
      fun i => Pi.single (pattern i) (r (pattern i) g (v i)) := by
    funext i
    exact action_single r g (pattern i) (v i)
  rw [hr, action_single] at h
  exact h

theorem restriction_compatible
    (f : MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := 1)) :
    TypedPatternAlternation.Compatible pattern (restriction r t pattern scalar f) := by
  intro p hp w
  let v : Fin n → ∀ s, V s := fun i => Pi.single (pattern i) (w i (pattern i))
  have he := (MixedSingleBosonDescent.extract n (representation r) (representation t) f).val.map_congr_perm v p
  have hv : v ∘ p = fun i => Pi.single (pattern i) (w (p i) (pattern i)) := by
    funext i
    have hi := congrFun hp i
    dsimp only [Function.comp_apply] at hi
    simp only [v, Function.comp_apply]
    rw [hi]
  rw [hv] at he
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun he.symm (Pi.single scalar x)

def familySpace : Submodule ℂ
    (MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := 1)) where
  carrier := {f | ∀ (labels : Fin n → P) (u : Q) (v : ∀ i, V (labels i)) (w : W u),
    (¬ ∃ p : Equiv.Perm (Fin n), labels ∘ p = pattern) ∨ u ≠ scalar →
      f (MixedWeightSupport.pure (fun i => Pi.single (labels i) (v i))
        (fun _ : Fin 1 => Pi.single u w)) = 0}
  zero_mem' := by intro labels u v w hh; rfl
  add_mem' := by
    intro f h hf hh labels u v w hout
    change f _ + h _ = 0
    rw [hf labels u v w hout, hh labels u v w hout, add_zero]
  smul_mem' := by
    intro z f hf labels u v w hout
    change z * f _ = 0
    rw [hf labels u v w hout, mul_zero]

theorem assemble_mem
    (k : MultilinearMap ℂ (fun i => V (pattern i)) (W scalar →ₗ[ℂ] ℂ))
    (hk : Invariant r t pattern scalar k) :
    assemble r t pattern scalar k hk ∈ familySpace r t pattern scalar := by
  intro labels u v w hout
  rcases hout with hout | hout
  · exact assemble_vanish_fermions r t pattern scalar k hk labels v _ hout
  · exact assemble_vanish_scalar r t pattern scalar k hk _ u w (Ne.symm hout)

theorem pure_perm
    (f : MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := 1))
    (v : Fin n → ∀ s, V s) (w : ∀ s, W s) (p : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign p • f (MixedWeightSupport.pure (v ∘ p) (fun _ : Fin 1 => w)) =
      f (MixedWeightSupport.pure v (fun _ : Fin 1 => w)) := by
  exact LinearMap.congr_fun
    ((MixedSingleBosonDescent.extract n (representation r) (representation t) f).val.map_congr_perm v p).symm w

theorem family_ext (f h : familySpace r t pattern scalar)
    (he : restriction r t pattern scalar f.val = restriction r t pattern scalar h.val) : f = h := by
  apply Subtype.ext
  apply Representation.IntertwiningMap.ext
  apply MixedSpeciesExt.ext
  intro labels scalars v w
  have hw : (fun j => Pi.single (scalars j) (w j)) =
      fun _ : Fin 1 => Pi.single (scalars 0) (w 0) := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  change f.val (MixedWeightSupport.pure _ _) = h.val (MixedWeightSupport.pure _ _)
  rw [hw]
  by_cases hout : (¬ ∃ p : Equiv.Perm (Fin n), labels ∘ p = pattern) ∨ scalars 0 ≠ scalar
  · rw [f.property labels (scalars 0) v (w 0) hout, h.property labels (scalars 0) v (w 0) hout]
  · push Not at hout
    obtain ⟨⟨p, hp⟩, hs⟩ := hout
    let z : Fin n → ∀ s, V s := fun i => Pi.single (labels i) (v i)
    have hz : (fun i => Pi.single (pattern i) (z (p i) (pattern i))) = z ∘ p := by
      funext i
      have hi := congrFun hp i
      dsimp only [Function.comp_apply] at hi
      have eta (u s : P) (x : V u) (h : u = s) :
          Pi.single s ((Pi.single u x) s) = Pi.single u x := by
        cases h
        simp
      exact eta (labels (p i)) (pattern i) (v (p i)) hi
    have hf := pure_perm r t f.val z (Pi.single (scalars 0) (w 0)) p
    have hh := pure_perm r t h.val z (Pi.single (scalars 0) (w 0)) p
    rw [← hf, ← hh]
    apply congrArg (Equiv.Perm.sign p • ·)
    have hn : (restriction r t pattern scalar f.val)
        (fun i => z (p i) (pattern i)) =
        (restriction r t pattern scalar h.val) (fun i => z (p i) (pattern i)) :=
      congrArg (fun k => k (fun i => z (p i) (pattern i))) he
    have hnw := LinearMap.congr_fun hn ((Pi.single (scalars 0) (w 0)) scalar)
    simp only [restriction_apply] at hnw
    rw [hz] at hnw
    have hsingle : Pi.single scalar ((Pi.single (scalars 0) (w 0)) scalar) =
        Pi.single (scalars 0) (w 0) := by
      have eta (u s : Q) (x : W u) (h : u = s) :
          Pi.single s ((Pi.single u x) s) = Pi.single u x := by
        cases h
        simp
      exact eta _ _ _ hs
    simpa only [hsingle] using hnw

 /-- Ordered maps with the actual group and identical-field exchange constraints. -/
def orderedSpace : Submodule ℂ
    (MultilinearMap ℂ (fun i => V (pattern i)) (W scalar →ₗ[ℂ] ℂ)) where
  carrier := {k | Invariant r t pattern scalar k ∧ TypedPatternAlternation.Compatible pattern k}
  zero_mem' := ⟨by intro g v w; rfl, by intro p hp v; simp [TypedPatternAlternation.ordered]⟩
  add_mem' := by
    intro k l hk hl
    constructor
    · intro g v w
      change k _ _ + l _ _ = k _ _ + l _ _
      rw [hk.1, hl.1]
    · intro p hp v
      change Equiv.Perm.sign p • (TypedPatternAlternation.ordered pattern k (v ∘ p) +
        TypedPatternAlternation.ordered pattern l (v ∘ p)) =
        TypedPatternAlternation.ordered pattern k v + TypedPatternAlternation.ordered pattern l v
      simpa only [smul_add] using
        congrArg₂ (· + ·) (hk.2 p hp v) (hl.2 p hp v)
  smul_mem' := by
    intro z k hk
    constructor
    · intro g v w
      change z * k _ _ = z * k _ _
      rw [hk.1]
    · intro p hp v
      change Equiv.Perm.sign p • (z • TypedPatternAlternation.ordered pattern k (v ∘ p)) =
        z • TypedPatternAlternation.ordered pattern k v
      rw [smul_comm, hk.2 p hp v]

/-- No spanning hypothesis is required: restriction and normalized assembly are inverse. -/
def equiv : familySpace r t pattern scalar ≃ₗ[ℂ] orderedSpace r t pattern scalar where
  toFun f := ⟨restriction r t pattern scalar f.val,
    restriction_invariant r t pattern scalar f.val,
    restriction_compatible r t pattern scalar f.val⟩
  invFun k := ⟨assemble r t pattern scalar k.val k.property.1,
    assemble_mem r t pattern scalar k.val k.property.1⟩
  left_inv f := by
    apply family_ext r t pattern scalar
    exact restriction_assemble_eq r t pattern scalar _
      (restriction_invariant r t pattern scalar f.val)
      (restriction_compatible r t pattern scalar f.val)
  right_inv k := by
    apply Subtype.ext
    exact restriction_assemble_eq r t pattern scalar k.val k.property.1 k.property.2
  map_add' f h := by
    apply Subtype.ext
    apply MultilinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    rfl
  map_smul' z f := by
    apply Subtype.ext
    apply MultilinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    rfl

end
end Math.MixedSinglePatternAssembly
