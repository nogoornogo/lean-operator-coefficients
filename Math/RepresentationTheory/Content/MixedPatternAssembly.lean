import Math.RepresentationTheory.Constructions.MixedPowerDescent
import Math.RepresentationTheory.Symmetric.TypedPatternSymmetrization
import Math.RepresentationTheory.Content.MixedSpeciesProjection

/-! Typed mixed pattern reconstruction, for arbitrary fermion and boson degrees. -/
namespace Math.MixedPatternAssembly
set_option autoImplicit false
noncomputable section
open Representation FiniteSpeciesExterior

private theorem single_eta {S : Type*} [DecidableEq S] {A : S → Type*}
    [∀ s, AddCommGroup (A s)] (u s : S) (x : A u) (hh : u = s) :
    Pi.single s ((Pi.single u x) s) = Pi.single u x := by cases hh; simp

variable {P Q G : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] [Group G]
  {V : P → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {W : Q → Type*} [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  (r : ∀ s, Representation ℂ G (V s)) (t : ∀ s, Representation ℂ G (W s))
  {n m : ℕ} (pattern : Fin n → P) (scalars : Fin m → Q)

abbrev Ordered := MultilinearMap ℂ (fun i => V (pattern i))
  (MultilinearMap ℂ (fun j => W (scalars j)) ℂ)

local notation "K" => Ordered (V := V) (W := W) pattern scalars

def Invariant (k : K) : Prop :=
  ∀ g v w, k (fun i => r (pattern i) g (v i))
    (fun j => t (scalars j) g (w j)) = k v w

def FermionCompatible (k : K) : Prop :=
  TypedPatternAlternation.Compatible pattern k

def BosonCompatible (k : K) : Prop :=
  ∀ v, TypedPatternSymmetrization.Compatible scalars (k v)

def lifted (k : K) :=
  (TypedPatternSymmetrization.linear scalars).compMultilinearMap k

def orderedExtension (k : K) :=
  TypedPatternAlternation.alternating pattern (lifted pattern scalars k)

omit [Fintype P] [DecidableEq P] [Fintype Q] in
theorem lifted_compatible (k : K) (hk : FermionCompatible pattern scalars k) :
    TypedPatternAlternation.Compatible pattern (lifted pattern scalars k) := by
  intro p hp v
  simpa only [lifted, TypedPatternAlternation.ordered, LinearMap.compMultilinearMap_apply,
    MultilinearMap.compLinearMap_apply, Units.smul_def, map_zsmul] using
    congrArg (TypedPatternSymmetrization.linear scalars) (hk p hp v)

omit [Fintype P] [Fintype Q] in
theorem orderedExtension_pure (k : K)
    (hf : FermionCompatible pattern scalars k) (hb : BosonCompatible pattern scalars k)
    (v : ∀ i, V (pattern i)) (w : ∀ j, W (scalars j)) :
    (orderedExtension pattern scalars k (fun i => Pi.single (pattern i) (v i))).val
      (fun j => Pi.single (scalars j) (w j)) = k v w := by
  rw [orderedExtension, TypedPatternAlternation.alternating_pure pattern _
    (lifted_compatible pattern scalars k hf)]
  exact TypedPatternSymmetrization.symmetric_pure scalars (k v) (hb v) w

theorem orderedExtension_invariant (k : K)
    (hk : Invariant r t pattern scalars k) :
    ∀ g v w, (orderedExtension pattern scalars k (representation r g ∘ v)).val
      (representation t g ∘ w) = (orderedExtension pattern scalars k v).val w := by
  intro g v w
  simp only [orderedExtension, TypedPatternAlternation.alternating,
    AlternatingMap.smul_apply, Submodule.coe_smul, smul_apply]
  congr 1
  simp only [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    Submodule.coe_sum, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ,
    Submodule.coe_smul, smul_apply, sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  simp only [TypedPatternAlternation.ordered, MultilinearMap.compLinearMap_apply,
    lifted, LinearMap.compMultilinearMap_apply,
    TypedPatternSymmetrization.linear, LinearMap.coe_mk, AddHom.coe_mk,
    TypedPatternSymmetrization.symmetric, smul_apply, sum_apply,
    MultilinearMap.domDomCongrLinearEquiv_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact hk g _ _

def assemble (k : K) (hk : Invariant r t pattern scalars k) :
    MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := m) :=
  MixedPowerDescent.descend n m (representation r) (representation t) (trivial ℂ G ℂ)
    ⟨orderedExtension pattern scalars k,
      orderedExtension_invariant r t pattern scalars k hk⟩

theorem restriction_assemble (k : K)
    (hk : Invariant r t pattern scalars k)
    (hf : FermionCompatible pattern scalars k) (hb : BosonCompatible pattern scalars k)
    (v : ∀ i, V (pattern i)) (w : ∀ j, W (scalars j)) :
    assemble r t pattern scalars k hk (MixedWeightSupport.pure
      (fun i => Pi.single (pattern i) (v i)) (fun j => Pi.single (scalars j) (w j))) = k v w := by
  change (MixedPowerDescent.orderedEquiv n m).symm (orderedExtension pattern scalars k) _ = _
  rw [MixedPowerDescent.lift_apply]
  exact orderedExtension_pure pattern scalars k hf hb v w

def restriction (f : MixedWeightSupport.Coefficient (representation r) (representation t)
    (n := n) (m := m)) : K :=
  (MultilinearMap.compLinearMapₗ (fun j => LinearMap.single ℂ W (scalars j))).compMultilinearMap
    ((MixedSpeciesProjection.raw f.toLinearMap).compLinearMap
      (fun i => LinearMap.single ℂ V (pattern i)))

@[simp] theorem restriction_apply
    (f : MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := m))
    (v : ∀ i, V (pattern i)) (w : ∀ j, W (scalars j)) :
    restriction r t pattern scalars f v w = f (MixedWeightSupport.pure
      (fun i => Pi.single (pattern i) (v i)) (fun j => Pi.single (scalars j) (w j))) := rfl

theorem restriction_assemble_eq (k : K) (hk : Invariant r t pattern scalars k)
    (hf : FermionCompatible pattern scalars k) (hb : BosonCompatible pattern scalars k) :
    restriction r t pattern scalars (assemble r t pattern scalars k hk) = k := by
  ext v w
  exact restriction_assemble r t pattern scalars k hk hf hb v w

theorem restriction_invariant
    (f : MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := m)) :
    Invariant r t pattern scalars (restriction r t pattern scalars f) := by
  intro g v w
  have he := IntertwiningMap.isIntertwining _ _ f g
    (MixedWeightSupport.pure (fun i => Pi.single (pattern i) (v i))
      (fun j => Pi.single (scalars j) (w j)))
  rw [MixedSpeciesProjection.action_pure r t] at he
  exact he

theorem restriction_fermion
    (f : MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := m)) :
    FermionCompatible pattern scalars (restriction r t pattern scalars f) := by
  intro p hp v
  ext w
  have he := MixedSpeciesProjection.pure_perm f.toLinearMap
    (fun i => Pi.single (pattern i) (v i (pattern i)))
    (fun j => Pi.single (scalars j) (w j)) p
  have hv : (fun i => Pi.single (pattern i) (v i (pattern i))) ∘ p =
      fun i => Pi.single (pattern i) (v (p i) (pattern i)) := by
    funext i
    have hi := congrFun hp i
    dsimp only [Function.comp_apply] at hi ⊢
    rw [hi]
  rw [hv] at he
  exact he

theorem restriction_boson
    (f : MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := m)) :
    BosonCompatible pattern scalars (restriction r t pattern scalars f) := by
  intro v p hp w
  have he := (MixedPowerDescent.orderedEquiv n m f.toLinearMap
    (fun i => Pi.single (pattern i) (v i))).property p
    (fun j => Pi.single (scalars j) (w j (scalars j)))
  have hw : (fun j => Pi.single (scalars j) (w j (scalars j))) ∘ p =
      fun j => Pi.single (scalars j) (w (p j) (scalars j)) := by
    funext j
    have hj := congrFun hp j
    dsimp only [Function.comp_apply] at hj ⊢
    rw [hj]
  rw [hw] at he
  exact he

def Orbit (labels : Fin n → P) (ss : Fin m → Q) : Prop :=
  (∃ p : Equiv.Perm (Fin n), labels ∘ p = pattern) ∧
  (∃ q : Equiv.Perm (Fin m), ss ∘ q = scalars)

def familySpace := MixedSpeciesProjection.supportSpace
  (Orbit pattern scalars) r t (n := n) (m := m)

theorem assemble_mem (k : K) (hk : Invariant r t pattern scalars k) :
    assemble r t pattern scalars k hk ∈ familySpace r t pattern scalars := by
  intro labels ss hout v w
  change (MixedPowerDescent.orderedEquiv n m).symm (orderedExtension pattern scalars k)
    (MixedWeightSupport.pure _ _) = 0
  rw [MixedPowerDescent.lift_apply]
  by_cases hl : ∃ p : Equiv.Perm (Fin n), labels ∘ p = pattern
  · have hs : ¬ ∃ q : Equiv.Perm (Fin m), ss ∘ q = scalars := fun hq => hout ⟨hl, hq⟩
    simp only [orderedExtension, TypedPatternAlternation.alternating,
      AlternatingMap.smul_apply, Submodule.coe_smul, smul_apply,
      MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
      Submodule.coe_sum, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ,
      Submodule.coe_smul, smul_apply, sum_apply]
    suffices hz : (∑ p : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign p : ℤ) : ℂ) •
          (TypedPatternSymmetrization.symmetric scalars
            (k (fun i => (Pi.single (labels (p i)) (v (p i))) (pattern i)))).val
              (fun j => Pi.single (ss j) (w j))) = 0 by
      change ((TypedPatternAlternation.stabilizer pattern).card : ℂ)⁻¹ •
        (∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤ) : ℂ) •
          (TypedPatternSymmetrization.symmetric scalars
            (k (fun i => (Pi.single (labels (p i)) (v (p i))) (pattern i)))).val
              (fun j => Pi.single (ss j) (w j))) = 0
      rw [hz, smul_zero]
    apply Finset.sum_eq_zero
    intro p _
    rw [TypedPatternSymmetrization.symmetric_vanish scalars _ ss w hs, smul_zero]
  · rw [orderedExtension, TypedPatternAlternation.alternating_vanish pattern _ labels v hl]
    rfl

theorem pure_perms
    (f : MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := m))
    (v : Fin n → ∀ s, V s) (w : Fin m → ∀ s, W s)
    (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign p • f (MixedWeightSupport.pure (v ∘ p) (w ∘ q)) =
      f (MixedWeightSupport.pure v w) := by
  have he := (MixedPowerDescent.orderedEquiv n m f.toLinearMap (v ∘ p)).property q w
  change f (MixedWeightSupport.pure (v ∘ p) (w ∘ q)) =
    f (MixedWeightSupport.pure (v ∘ p) w) at he
  rw [he]
  exact MixedSpeciesProjection.pure_perm f.toLinearMap v w p

theorem family_ext (f h : familySpace r t pattern scalars)
    (he : restriction r t pattern scalars f.val = restriction r t pattern scalars h.val) : f = h := by
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply MixedSpeciesExt.ext
  intro labels ss v w
  change f.val (MixedWeightSupport.pure _ _) = h.val (MixedWeightSupport.pure _ _)
  by_cases hout : Orbit pattern scalars labels ss
  · obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hout
    let z : Fin n → ∀ s, V s := fun i => Pi.single (labels i) (v i)
    let y : Fin m → ∀ s, W s := fun j => Pi.single (ss j) (w j)
    have hz : (fun i => Pi.single (pattern i) (z (p i) (pattern i))) = z ∘ p := by
      funext i
      exact single_eta _ _ _ (congrFun hp i)
    have hy : (fun j => Pi.single (scalars j) (y (q j) (scalars j))) = y ∘ q := by
      funext j
      exact single_eta _ _ _ (congrFun hq j)
    rw [← pure_perms r t f.val z y p q, ← pure_perms r t h.val z y p q]
    apply congrArg (Equiv.Perm.sign p • ·)
    have hh := congrArg (fun k : K =>
      k (fun i => z (p i) (pattern i)) (fun j => y (q j) (scalars j))) he
    simp only [restriction_apply] at hh
    simpa only [hz, hy] using hh
  · rw [f.property labels ss hout v w, h.property labels ss hout v w]

def orderedSpace : Submodule ℂ K where
  carrier := {k | Invariant r t pattern scalars k ∧
    FermionCompatible pattern scalars k ∧ BosonCompatible pattern scalars k}
  zero_mem' := ⟨by intro g v w; rfl,
    by intro p hp v; simp [TypedPatternAlternation.ordered],
    by intro v p hp w; rfl⟩
  add_mem' := by
    intro k l hk hl
    refine ⟨?_, ?_, ?_⟩
    · intro g v w
      change k _ _ + l _ _ = k _ _ + l _ _
      rw [hk.1, hl.1]
    · intro p hp v
      change Equiv.Perm.sign p • (TypedPatternAlternation.ordered pattern k (v ∘ p) +
        TypedPatternAlternation.ordered pattern l (v ∘ p)) = _
      rw [smul_add, hk.2.1 p hp, hl.2.1 p hp]
      rfl
    · intro v p hp w
      change TypedPatternSymmetrization.ordered scalars (k v) (w ∘ p) +
        TypedPatternSymmetrization.ordered scalars (l v) (w ∘ p) = _
      rw [hk.2.2 v p hp, hl.2.2 v p hp]
      rfl
  smul_mem' := by
    intro z k hk
    refine ⟨?_, ?_, ?_⟩
    · intro g v w
      change z • k _ _ = z • k _ _
      rw [hk.1]
    · intro p hp v
      change Equiv.Perm.sign p • (z • TypedPatternAlternation.ordered pattern k (v ∘ p)) = _
      rw [smul_comm, hk.2.1 p hp]
      rfl
    · intro v p hp w
      change z • TypedPatternSymmetrization.ordered scalars (k v) (w ∘ p) = _
      rw [hk.2.2 v p hp]
      rfl

def equiv : familySpace r t pattern scalars ≃ₗ[ℂ] orderedSpace r t pattern scalars where
  toFun f := ⟨restriction r t pattern scalars f.val,
    restriction_invariant r t pattern scalars f.val,
    restriction_fermion r t pattern scalars f.val,
    restriction_boson r t pattern scalars f.val⟩
  invFun k := ⟨assemble r t pattern scalars k.val k.property.1,
    assemble_mem r t pattern scalars k.val k.property.1⟩
  left_inv f := by
    apply family_ext r t pattern scalars
    exact restriction_assemble_eq r t pattern scalars _
      (restriction_invariant r t pattern scalars f.val)
      (restriction_fermion r t pattern scalars f.val)
      (restriction_boson r t pattern scalars f.val)
  right_inv k := by
    apply Subtype.ext
    exact restriction_assemble_eq r t pattern scalars k.val
      k.property.1 k.property.2.1 k.property.2.2
  map_add' f h := by apply Subtype.ext; ext v w; rfl
  map_smul' z f := by apply Subtype.ext; ext v w; rfl

end
end Math.MixedPatternAssembly
