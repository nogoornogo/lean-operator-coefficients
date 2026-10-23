import Math.RepresentationTheory.Content.MixedSinglePatternAssembly

/-! Permutation-stable support projection on the independent single-boson input. -/
namespace Math.MixedSingleSpeciesProjection
set_option autoImplicit false
noncomputable section
open Representation FiniteSpeciesExterior MixedSinglePatternAssembly
variable {P Q G : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] [Group G]
  {V : P → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {W : Q → Type*} [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  (r : ∀ s, Representation ℂ G (V s)) (t : ∀ s, Representation ℂ G (W s))
  {n : ℕ} (support : (Fin n → P) → Q → Prop)
  [∀ labels, DecidablePred (support labels)]

abbrev Coefficient := MixedWeightSupport.Coefficient (representation r) (representation t)
  (n := n) (m := 1)

def cutMultilinear (f : Coefficient r t (n := n)) :
    MultilinearMap ℂ (fun _ : Fin n => ∀ s, V s) ((∀ s, W s) →ₗ[ℂ] ℂ) :=
  ∑ x : (Fin n → P) × Q, if support x.1 x.2 then
    TypedPatternAlternation.ordered x.1
      (lifted x.1 x.2 (restriction r t x.1 x.2 f)) else 0

theorem cutMultilinear_pure (f : Coefficient r t (n := n)) (labels : Fin n → P)
    (u : Q) (v : ∀ i, V (labels i)) (w : W u) :
    cutMultilinear r t support f (fun i => Pi.single (labels i) (v i)) (Pi.single u w) =
      if support labels u then f (MixedWeightSupport.pure
        (fun i => Pi.single (labels i) (v i)) (fun _ : Fin 1 => Pi.single u w)) else 0 := by
  classical
  rw [cutMultilinear, sum_apply, LinearMap.sum_apply, Finset.sum_eq_single (labels, u)]
  · by_cases hh : support labels u <;>
      simp [hh, TypedPatternAlternation.ordered, lifted, spectatorLift]
  · intro x _ hx
    by_cases hp : support x.1 x.2
    · simp only [hp, ite_true, TypedPatternAlternation.ordered,
        MultilinearMap.compLinearMap_apply, LinearMap.proj_apply]
      by_cases hs : x.2 = u
      · have hl : x.1 ≠ labels := by
          intro he
          exact hx (Prod.ext he hs)
        obtain ⟨i, hi⟩ : ∃ i, x.1 i ≠ labels i := by
          by_contra hn
          exact hl (funext (fun i => by simpa using not_exists.mp hn i))
        have hz : (lifted x.1 x.2 (restriction r t x.1 x.2 f))
            (fun i => (Pi.single (labels i) (v i)) (x.1 i)) = 0 := by
          apply MultilinearMap.map_coord_zero _ i
          exact Pi.single_eq_of_ne hi _
        rw [hz]
        rfl
      · change (restriction r t x.1 x.2 f) _ ((Pi.single u w) x.2) = 0
        rw [Pi.single_eq_of_ne hs]
        exact map_zero _
    · simp [hp]
  · simp

def cutAlternating (f : Coefficient r t (n := n)) :=
  ((Nat.factorial n : ℂ)⁻¹) • (cutMultilinear r t support f).alternatization

variable (stable : ∀ labels u (p : Equiv.Perm (Fin n)),
  support (labels ∘ p) u ↔ support labels u)

private theorem signed_ite {a b : Prop} [Decidable a] [Decidable b]
    (hab : a ↔ b) (z : ℤˣ) (x y : ℂ) (hxy : z • x = y) :
    z • (if a then x else 0) = if b then y else 0 := by
  by_cases hb : b
  · simp only [ite_eq_left (hab.mpr hb), ite_eq_left hb, hxy]
  · simp only [ite_eq_right (fun ha => hb (hab.mp ha)), ite_eq_right hb, smul_zero]

include stable in
theorem cutAlternating_pure (f : Coefficient r t (n := n)) (labels : Fin n → P)
    (u : Q) (v : ∀ i, V (labels i)) (w : W u) :
    cutAlternating r t support f (fun i => Pi.single (labels i) (v i)) (Pi.single u w) =
      if support labels u then f (MixedWeightSupport.pure
        (fun i => Pi.single (labels i) (v i)) (fun _ : Fin 1 => Pi.single u w)) else 0 := by
  classical
  simp only [cutAlternating, AlternatingMap.smul_apply, LinearMap.smul_apply,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    LinearMap.sum_apply]
  have ht (p : Equiv.Perm (Fin n)) :
      (Equiv.Perm.sign p • cutMultilinear r t support f
        (fun i => Pi.single (labels (p i)) (v (p i)))) (Pi.single u w) =
        if support labels u then f (MixedWeightSupport.pure
          (fun i => Pi.single (labels i) (v i)) (fun _ : Fin 1 => Pi.single u w)) else 0 := by
    change Equiv.Perm.sign p • (cutMultilinear r t support f _ _) = _
    have hp : support (fun i => labels (p i)) u ↔ support labels u := stable labels u p
    calc
      _ = Equiv.Perm.sign p • (if support (fun i => labels (p i)) u then
          f (MixedWeightSupport.pure
            (fun i => Pi.single (labels (p i)) (v (p i)))
            (fun _ : Fin 1 => Pi.single u w)) else 0) :=
        congrArg (Equiv.Perm.sign p • ·)
          (cutMultilinear_pure r t support f (labels ∘ p) u (fun i => v (p i)) w)
      _ = _ := signed_ite hp (Equiv.Perm.sign p) _ _
        (pure_perm r t f (fun i => Pi.single (labels i) (v i)) (Pi.single u w) p)
  change (Nat.factorial n : ℂ)⁻¹ * (∑ p : Equiv.Perm (Fin n),
    (Equiv.Perm.sign p • cutMultilinear r t support f
      (fun i => Pi.single (labels (p i)) (v (p i)))) (Pi.single u w)) = _
  simp_rw [ht]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n), one_mul]

theorem cutMultilinear_invariant (f : Coefficient r t (n := n))
    (g : G) (v : Fin n → ∀ s, V s) (w : ∀ s, W s) :
    cutMultilinear r t support f (representation r g ∘ v) (representation t g w) =
      cutMultilinear r t support f v w := by
  simp only [cutMultilinear, sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs
  · exact restriction_invariant r t x.1 x.2 f g _ _
  · rfl

theorem cutAlternating_invariant (f : Coefficient r t (n := n))
    (g : G) (v : Fin n → ∀ s, V s) (w : ∀ s, W s) :
    cutAlternating r t support f (representation r g ∘ v) (representation t g w) =
      cutAlternating r t support f v w := by
  simp only [cutAlternating, AlternatingMap.smul_apply, LinearMap.smul_apply]
  congr 1
  simp only [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  exact cutMultilinear_invariant r t support f g (v ∘ p) w

def project (f : Coefficient r t (n := n)) : Coefficient r t (n := n) :=
  MixedSingleBosonDescent.descend n (representation r) (representation t)
    ⟨cutAlternating r t support f, cutAlternating_invariant r t support f⟩

theorem coefficient_ext (f h : Coefficient r t (n := n))
    (he : ∀ (labels : Fin n → P) (u : Q) (v : ∀ i, V (labels i)) (w : W u),
      f (MixedWeightSupport.pure (fun i => Pi.single (labels i) (v i))
          (fun _ : Fin 1 => Pi.single u w)) =
        h (MixedWeightSupport.pure (fun i => Pi.single (labels i) (v i))
          (fun _ : Fin 1 => Pi.single u w))) : f = h := by
  apply Representation.IntertwiningMap.ext
  apply MixedSpeciesExt.ext
  intro labels scalars v w
  have hw : (fun j => Pi.single (scalars j) (w j)) =
      fun _ : Fin 1 => Pi.single (scalars 0) (w 0) := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  change f (MixedWeightSupport.pure _ _) = h (MixedWeightSupport.pure _ _)
  rw [hw]
  exact he labels (scalars 0) v (w 0)

include stable in
theorem project_pure (f : Coefficient r t (n := n)) (labels : Fin n → P)
    (u : Q) (v : ∀ i, V (labels i)) (w : W u) :
    project r t support f (MixedWeightSupport.pure
      (fun i => Pi.single (labels i) (v i)) (fun _ : Fin 1 => Pi.single u w)) =
      if support labels u then f (MixedWeightSupport.pure
        (fun i => Pi.single (labels i) (v i)) (fun _ : Fin 1 => Pi.single u w)) else 0 := by
  change (MixedSingleBosonDescent.orderedEquiv n).symm (cutAlternating r t support f) _ = _
  rw [MixedSingleBosonDescent.lift_apply]
  exact cutAlternating_pure r t support stable f labels u v w

include stable in
theorem project_idempotent (f : Coefficient r t (n := n)) :
    project r t support (project r t support f) = project r t support f := by
  apply Representation.IntertwiningMap.ext
  apply MixedSpeciesExt.ext
  intro labels scalars v w
  have hw : (fun j => Pi.single (scalars j) (w j)) =
      fun _ : Fin 1 => Pi.single (scalars 0) (w 0) := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  change project r t support (project r t support f) (MixedWeightSupport.pure _ _) =
    project r t support f (MixedWeightSupport.pure _ _)
  rw [hw]
  simp only [project_pure r t support stable]
  split_ifs <;> rfl

def supportSpace : Submodule ℂ (Coefficient r t (n := n)) where
  carrier := {f | ∀ (labels : Fin n → P) (u : Q) (v : ∀ i, V (labels i)) (w : W u),
    ¬ support labels u → f (MixedWeightSupport.pure
      (fun i => Pi.single (labels i) (v i)) (fun _ : Fin 1 => Pi.single u w)) = 0}
  zero_mem' := by intro labels u v w hh; rfl
  add_mem' := by
    intro f h hf hh labels u v w hout
    change f _ + h _ = 0
    rw [hf labels u v w hout, hh labels u v w hout, add_zero]
  smul_mem' := by
    intro z f hf labels u v w hout
    change z * f _ = 0
    rw [hf labels u v w hout, mul_zero]

include stable in
theorem project_mem (f : Coefficient r t (n := n)) :
    project r t support f ∈ supportSpace r t support := by
  intro labels u v w hout
  rw [project_pure r t support stable, ite_eq_right hout]

include stable in
theorem project_eq_self (f : supportSpace r t support) :
    project r t support f.val = f.val := by
  apply coefficient_ext r t
  intro labels u v w
  rw [project_pure r t support stable]
  split_ifs with hs
  · rfl
  · exact (f.property labels u v w hs).symm

def projectLinear : Coefficient r t (n := n) →ₗ[ℂ] Coefficient r t (n := n) where
  toFun := project r t support
  map_add' f h := by
    apply coefficient_ext r t
    intro labels u v w
    change project r t support (f + h) _ = project r t support f _ + project r t support h _
    simp only [project_pure r t support stable]
    split_ifs
    · rfl
    · exact (add_zero _).symm
  map_smul' z f := by
    apply coefficient_ext r t
    intro labels u v w
    change project r t support (z • f) _ = z * project r t support f _
    simp only [project_pure r t support stable]
    split_ifs
    · rfl
    · exact (mul_zero _).symm

include stable in
theorem project_add (f h : Coefficient r t (n := n)) :
    project r t support (f + h) = project r t support f + project r t support h :=
  (projectLinear r t support stable).map_add f h

include stable in
theorem project_smul (z : ℂ) (f : Coefficient r t (n := n)) :
    project r t support (z • f) = z • project r t support f :=
  (projectLinear r t support stable).map_smul z f

-- Consumers use the proved equations rather than expanding the finite species sum.
attribute [irreducible] project

end
end Math.MixedSingleSpeciesProjection
