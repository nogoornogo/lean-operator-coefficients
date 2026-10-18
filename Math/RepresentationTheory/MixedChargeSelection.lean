import Math.RepresentationTheory.MixedScalarSelection
import Math.RepresentationTheory.CyclicCharge

/-! Arbitrary abelian charge vectors, including simultaneous B/L/flavor labels.
Characters obstruct invariants; neutral charge does not construct invariants. -/
namespace Math.MixedChargeSelection
set_option autoImplicit false
noncomputable section
open Representation
open scoped BigOperators

variable {A P Q : Type*} [AddCommGroup A] {n m : ℕ}

def charge (fq : P → A) (bq : Q → A) (p : Fin n → P) (s : Fin m → Q) : A :=
  (∑ i, fq (p i)) + ∑ j, bq (s j)

theorem charge_stable (fq : P → A) (bq : Q → A) (p : Fin n → P) (s : Fin m → Q)
    (e : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin m)) :
    charge fq bq (p ∘ e) (s ∘ f) = charge fq bq p s := by
  unfold charge
  congr 1
  · exact Fintype.sum_equiv e _ _ (by intro i; rfl)
  · exact Fintype.sum_equiv f _ _ (by intro i; rfl)

private theorem char_sum {I : Type*} [Fintype I] (chi : AddChar A ℂ) (v : I → A) :
    chi (∑ i, v i) = ∏ i, chi (v i) := by
  classical
  have h : ∀ t : Finset I, chi (∑ i ∈ t, v i) = ∏ i ∈ t, chi (v i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih => simp [hi, AddChar.map_add_eq_mul, ih]
  exact h Finset.univ

theorem total_eq_character (chi : AddChar A ℂ) (fq : P → A) (bq : Q → A)
    (p : Fin n → P) (s : Fin m → Q) :
    MixedScalarSelection.total p s (fun u => chi (fq u)) (fun u => chi (bq u)) =
      chi (charge fq bq p s) := by
  simp only [MixedScalarSelection.total, charge, AddChar.map_add_eq_mul, char_sum]

/-- Zero fermion and boson degrees have neutral charge. -/
theorem charge_zero (fq : P → A) (bq : Q → A) (p : Fin 0 → P) (s : Fin 0 → Q) :
    charge fq bq p s = 0 := by simp [charge]

/-- Conjugate labels cancel in a paired charge sum. -/
theorem conjugate_charge (q : A) : charge (fun _ : Unit => q) (fun _ : Unit => -q)
    (fun _ : Fin 1 => ()) (fun _ : Fin 1 => ()) = 0 := by simp [charge]

section Mixed
variable {G H : Type*} [Group G] [Group H]
  [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {L M : P → Type*} {K N : Q → Type*}
  [∀ u, AddCommGroup (L u)] [∀ u, Module ℂ (L u)]
  [∀ u, AddCommGroup (M u)] [∀ u, Module ℂ (M u)]
  [∀ u, AddCommGroup (K u)] [∀ u, Module ℂ (K u)]
  [∀ u, AddCommGroup (N u)] [∀ u, Module ℂ (N u)]
  (a : ∀ u, Representation ℂ G (L u)) (b : ∀ u, Representation ℂ G (K u))
  (c : ∀ u, Representation ℂ H (M u)) (d : ∀ u, Representation ℂ H (N u))
  (fq : P → A) (bq : Q → A) (chi : H → AddChar A ℂ)
  (hf : ∀ g u v, c u g v = chi g (fq u) • v)
  (hb : ∀ g u v, d u g v = chi g (bq u) • v)
  (allowed : ∀ n m : ℕ, (Fin n → P) → (Fin m → Q) → Prop)
  [∀ n m p s, Decidable (allowed n m p s)]
  (stable : ∀ n m p s (e : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin m)),
    allowed n m (p ∘ e) (s ∘ f) ↔ allowed n m p s)

include hf hb stable in
theorem all_forbidden
    (detect : ∀ n m (p : Fin n → P) (s : Fin m → Q), allowed n m p s →
      ∃ g, chi g (charge fq bq p s) ≠ 1) :
    ∀ n m, ∀ f : MixedSpeciesProjection.supportSpace (allowed n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0 := by
  apply MixedScalarSelection.all_forbidden a b c d allowed stable
  intro n m p s hp
  obtain ⟨g,hg⟩ := detect n m p s hp
  exact ⟨g, (fun u => chi g (fq u)), (fun u => chi g (bq u)), hf g, hb g,
    by rwa [total_eq_character]⟩
end Mixed

/-- Integer charges evaluated on the circle; no topological assumption is
needed by the algebraic obstruction theorem. -/
def circleCharacter (z : Circle) : AddChar ℤ ℂ where
  toFun q := (z : ℂ) ^ q
  map_zero_eq_one' := by simp
  map_add_eq_mul' q r := zpow_add₀ (Circle.coe_ne_zero z) q r

@[simp] theorem circle_conjugate (z : Circle) (q : ℤ) :
    circleCharacter z q * circleCharacter z (-q) = 1 := by
  rw [← (circleCharacter z).map_add_eq_mul]
  simp

section Cyclic
variable {k : ℕ} [NeZero k]

def cyclicCharacter (g : CyclicCharge.Group k) : AddChar (ZMod k) ℂ where
  toFun q := ZMod.stdAddChar (q * Multiplicative.toAdd g)
  map_zero_eq_one' := by simp
  map_add_eq_mul' q r := by simp [add_mul, AddChar.map_add_eq_mul]

theorem cyclic_detect_iff (q : ZMod k) :
    (∃ g : CyclicCharge.Group k, cyclicCharacter g q ≠ 1) ↔ q ≠ 0 := by
  change (∃ g : CyclicCharge.Group k, ZMod.stdAddChar (q * Multiplicative.toAdd g) ≠ 1) ↔ q ≠ 0
  simpa only [not_forall, not_not] using
    not_congr (CyclicCharge.neutral_iff q)
end Cyclic
end
end Math.MixedChargeSelection
