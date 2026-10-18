import Math.RepresentationTheory.MixedPowerDescent
import Math.RepresentationTheory.MixedSpeciesExt
import Math.RepresentationTheory.SymmetricMultilinearProjection

/-! Species support on arbitrary mixed exterior/symmetric input. -/
namespace Math.MixedSpeciesProjection
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {V : P → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {W : Q → Type*} [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  {n m : ℕ}

abbrev Domain := MixedSpeciesExt.Carrier (V := V) (W := W) (n := n) (m := m)
abbrev Raw := MultilinearMap ℂ (fun _ : Fin n => ∀ s, V s)
  (MultilinearMap ℂ (fun _ : Fin m => ∀ s, W s) ℂ)

def mask {I : Type*} [DecidableEq I] {A : I → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] (s : I) :
    (∀ i, A i) →ₗ[ℂ] (∀ i, A i) := (LinearMap.single ℂ A s).comp (LinearMap.proj s)

def raw (f : Domain (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ) :
    Raw (V := V) (W := W) (n := n) (m := m) :=
  ((SymmetricPowerDescent.symmetricMaps (A := ∀ s, W s) (N := ℂ) m).subtype.compAlternatingMap
    (MixedPowerDescent.orderedEquiv n m f)).toMultilinearMap

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
@[simp] theorem raw_apply (f : Domain (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ)
    (v : Fin n → ∀ s, V s) (w : Fin m → ∀ s, W s) :
    raw f v w = f (MixedWeightSupport.pure v w) := rfl

variable (support : (Fin n → P) → (Fin m → Q) → Prop)
  [∀ labels scalars, Decidable (support labels scalars)]

def cut (f : Domain (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ) :
    Raw (V := V) (W := W) (n := n) (m := m) :=
  ∑ x : (Fin n → P) × (Fin m → Q), if support x.1 x.2 then
    (MultilinearMap.compLinearMapₗ (fun j => mask (x.2 j))).compMultilinearMap
      ((raw f).compLinearMap (fun i => mask (x.1 i))) else 0

theorem cut_pure (f : Domain (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ)
    (labels : Fin n → P) (scalars : Fin m → Q)
    (v : ∀ i, V (labels i)) (w : ∀ j, W (scalars j)) :
    cut support f (fun i => Pi.single (labels i) (v i))
      (fun j => Pi.single (scalars j) (w j)) =
    if support labels scalars then f (MixedWeightSupport.pure
      (fun i => Pi.single (labels i) (v i)) (fun j => Pi.single (scalars j) (w j))) else 0 := by
  rw [cut, sum_apply, sum_apply,
    Finset.sum_eq_single (labels,scalars)]
  · by_cases hs : support labels scalars <;>
      simp [hs, mask, MultilinearMap.compLinearMap_apply, raw_apply]
  · intro x _ hx
    by_cases hs : support x.1 x.2
    · simp only [hs, ite_true, LinearMap.compMultilinearMap_apply,
        MultilinearMap.compLinearMap_apply, MultilinearMap.compLinearMapₗ_apply]
      by_cases hl : x.1 = labels
      · have hw : x.2 ≠ scalars := by intro he; exact hx (Prod.ext hl he)
        obtain ⟨j,hj⟩ : ∃ j, x.2 j ≠ scalars j := by
          by_contra hn
          exact hw (funext (fun j => by simpa using not_exists.mp hn j))
        apply MultilinearMap.map_coord_zero _ j
        simp [mask, Pi.single_eq_of_ne hj]
      · obtain ⟨i,hi⟩ : ∃ i, x.1 i ≠ labels i := by
          by_contra hn
          exact hl (funext (fun i => by simpa using not_exists.mp hn i))
        have hz : raw f (fun i => mask (x.1 i) (Pi.single (labels i) (v i))) = 0 := by
          apply MultilinearMap.map_coord_zero _ i
          simp [mask, Pi.single_eq_of_ne hi]
        rw [hz]
        rfl
    · simp [hs]
  · simp

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem pure_perm (f : Domain (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ)
    (v : Fin n → ∀ s, V s) (w : Fin m → ∀ s, W s) (p : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign p • f (MixedWeightSupport.pure (v ∘ p) w) =
      f (MixedWeightSupport.pure v w) := by
  have he := congrArg (fun q : SymmetricPowerDescent.symmetricMaps (A := ∀ s, W s) (N := ℂ) m =>
    q.val w) ((MixedPowerDescent.orderedEquiv n m f).map_congr_perm v p).symm
  exact he

def ordered (f : Domain (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ) :=
  (SymmetricMultilinearProjection.project m).compAlternatingMap
    (((Nat.factorial n : ℂ)⁻¹) • (cut support f).alternatization)

def project (f : Domain (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ) :
    Domain (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ :=
  (MixedPowerDescent.orderedEquiv n m).symm (ordered support f)

variable (stable : ∀ labels scalars (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin m)),
  support (labels ∘ p) (scalars ∘ q) ↔ support labels scalars)

include stable in
theorem project_pure (f : Domain (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ)
    (labels : Fin n → P) (scalars : Fin m → Q)
    (v : ∀ i, V (labels i)) (w : ∀ j, W (scalars j)) :
    project support f (MixedWeightSupport.pure (fun i => Pi.single (labels i) (v i))
      (fun j => Pi.single (scalars j) (w j))) =
    if support labels scalars then f (MixedWeightSupport.pure
      (fun i => Pi.single (labels i) (v i)) (fun j => Pi.single (scalars j) (w j))) else 0 := by
  let vv := fun i => Pi.single (labels i) (v i)
  let ww := fun j => Pi.single (scalars j) (w j)
  have ht (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin m)) :
      Equiv.Perm.sign p • cut support f (vv ∘ p) (ww ∘ q) =
      if support labels scalars then f (MixedWeightSupport.pure vv ww) else 0 := by
    have he := cut_pure support f (labels ∘ p) (scalars ∘ q)
      (fun i => v (p i)) (fun j => w (q j))
    change cut support f (vv ∘ p) (ww ∘ q) =
      (if support (labels ∘ p) (scalars ∘ q) then
        f (MixedWeightSupport.pure (vv ∘ p) (ww ∘ q)) else 0) at he
    rw [he]
    by_cases hs : support labels scalars
    · rw [ite_eq_left ((stable labels scalars p q).mpr hs), ite_eq_left hs,
        pure_perm f vv (ww ∘ q) p]
      exact (MixedPowerDescent.orderedEquiv n m f vv).property q ww
    · rw [ite_eq_right (fun h => hs ((stable labels scalars p q).mp h)),
        ite_eq_right hs, smul_zero]
  rw [project, MixedPowerDescent.lift_apply]
  change SymmetricMultilinearProjection.raw m
    (((Nat.factorial n : ℂ)⁻¹ • (cut support f).alternatization) vv) ww = _
  rw [SymmetricMultilinearProjection.raw_apply]
  simp only [AlternatingMap.smul_apply, smul_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, sum_apply]
  change (Nat.factorial m : ℂ)⁻¹ • ∑ q : Equiv.Perm (Fin m),
    (Nat.factorial n : ℂ)⁻¹ • ∑ p : Equiv.Perm (Fin n),
      Equiv.Perm.sign p • cut support f (vv ∘ p) (ww ∘ q) = _
  simp_rw [ht]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n), mul_one,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero m), one_smul]

section Equivariant
open Representation FiniteSpeciesExterior
variable {G : Type*} [Group G]
  (r : ∀ s, Representation ℂ G (V s)) (t : ∀ s, Representation ℂ G (W s))

abbrev Coefficient := MixedWeightSupport.Coefficient (representation r) (representation t)
  (n := n) (m := m)

theorem action_pure (g : G) (labels : Fin n → P) (scalars : Fin m → Q)
    (v : ∀ i, V (labels i)) (w : ∀ j, W (scalars j)) :
    (((representation r).exteriorPower n).tprod ((representation t).symmetricPower m)) g
      (MixedWeightSupport.pure (fun i => Pi.single (labels i) (v i))
        (fun j => Pi.single (scalars j) (w j))) =
    MixedWeightSupport.pure (fun i => Pi.single (labels i) (r (labels i) g (v i)))
      (fun j => Pi.single (scalars j) (t (scalars j) g (w j))) := by
  simp only [MixedWeightSupport.pure, Representation.tprod_apply, TensorProduct.map_tmul,
    Representation.exteriorPower_apply_ιMulti, Representation.symmetricPower_apply_tprod]
  congr 1
  · congr 1
    funext i
    exact action_single r g (labels i) (v i)
  · congr 1
    funext j
    exact action_single t g (scalars j) (w j)

include stable in
def invariantProject (f : Coefficient r t (n := n) (m := m)) : Coefficient r t (n := n) (m := m) where
  toLinearMap := project support f.toLinearMap
  isIntertwining' g := by
    apply MixedSpeciesExt.ext
    intro labels scalars v w
    change project support f.toLinearMap
      ((((representation r).exteriorPower n).tprod ((representation t).symmetricPower m)) g
        (MixedWeightSupport.pure _ _)) =
      project support f.toLinearMap (MixedWeightSupport.pure _ _)
    rw [action_pure r t, project_pure support stable, project_pure support stable]
    by_cases hs : support labels scalars
    · simp only [hs, ite_true]
      have he := IntertwiningMap.isIntertwining _ _ f g
        (MixedWeightSupport.pure (fun i => Pi.single (labels i) (v i))
          (fun j => Pi.single (scalars j) (w j)))
      rw [action_pure r t] at he
      exact he
    · simp [hs]

def supportSpace : Submodule ℂ (Coefficient r t (n := n) (m := m)) where
  carrier := {f | ∀ labels scalars, ¬ support labels scalars →
    ∀ (v : ∀ i, V (labels i)) (w : ∀ j, W (scalars j)),
    f (MixedWeightSupport.pure (fun i => Pi.single (labels i) (v i))
      (fun j => Pi.single (scalars j) (w j))) = 0}
  zero_mem' := by intro labels scalars hs v w; rfl
  add_mem' := by
    intro f q hf hq labels scalars hs v w
    change f _ + q _ = 0
    rw [hf labels scalars hs, hq labels scalars hs, add_zero]
  smul_mem' := by
    intro z f hf labels scalars hs v w
    change z • f _ = 0
    rw [hf labels scalars hs, smul_zero]

include stable in
theorem project_mem (f : Coefficient r t (n := n) (m := m)) :
    invariantProject support stable r t f ∈ supportSpace support r t := by
  intro labels scalars hs v w
  change project support f.toLinearMap (MixedWeightSupport.pure _ _) = 0
  rw [project_pure support stable, ite_eq_right hs]

include stable in
theorem project_eq_self (f : supportSpace support r t (n := n) (m := m)) :
    invariantProject support stable r t f.val = f.val := by
  apply IntertwiningMap.ext
  apply MixedSpeciesExt.ext
  intro labels scalars v w
  change project support f.val.toLinearMap (MixedWeightSupport.pure _ _) = f.val _
  rw [project_pure support stable]
  by_cases hs : support labels scalars
  · rw [ite_eq_left hs]; rfl
  · rw [ite_eq_right hs]
    exact (f.property labels scalars hs v w).symm

include stable in
def projectLinear : Coefficient r t (n := n) (m := m) →ₗ[ℂ] Coefficient r t (n := n) (m := m) where
  toFun := invariantProject support stable r t
  map_add' f q := by
    apply IntertwiningMap.ext
    apply MixedSpeciesExt.ext
    intro labels scalars v w
    change project support (f+q).toLinearMap (MixedWeightSupport.pure _ _) =
      project support f.toLinearMap (MixedWeightSupport.pure _ _) +
        project support q.toLinearMap (MixedWeightSupport.pure _ _)
    rw [project_pure support stable, project_pure support stable, project_pure support stable]
    by_cases hs : support labels scalars <;> simp [hs]
  map_smul' z f := by
    apply IntertwiningMap.ext
    apply MixedSpeciesExt.ext
    intro labels scalars v w
    change project support (z • f).toLinearMap (MixedWeightSupport.pure _ _) =
      z • project support f.toLinearMap (MixedWeightSupport.pure _ _)
    rw [project_pure support stable, project_pure support stable]
    by_cases hs : support labels scalars <;> simp [hs]

end Equivariant

end
end Math.MixedSpeciesProjection
