import Math.RepresentationTheory.TypedSymmetricPatternHom
import Math.RepresentationTheory.SymmetricPowerOperations
import Mathlib.GroupTheory.Perm.Subgroup

/-! Canonical two-species blocks and their exact permutation stabilizer. -/
namespace Math.TwoSpeciesPattern
set_option autoImplicit false
noncomputable section
def pattern (h d : ℕ) : Fin (h+d) → Fin 2 :=
  Sum.elim (fun _ : Fin h => 0) (fun _ : Fin d => 1) ∘ finSumFinEquiv.symm

def left {h d : ℕ} (i : Fin h) : Fin (h+d) := finSumFinEquiv (Sum.inl i)
def right {h d : ℕ} (i : Fin d) : Fin (h+d) := finSumFinEquiv (Sum.inr i)

@[simp] theorem pattern_left (h d : ℕ) (i : Fin h) : pattern h d (left i) = 0 := by
  simp [pattern,left]
@[simp] theorem pattern_right (h d : ℕ) (i : Fin d) : pattern h d (right i) = 1 := by
  simp [pattern,right]

def leftFiber (h d : ℕ) : Fin h ≃ {i : Fin (h+d) // pattern h d i = 0} :=
  Equiv.ofBijective (fun i => ⟨left i,pattern_left h d i⟩) ⟨by
    intro i j he
    exact Sum.inl.inj (finSumFinEquiv.injective (congrArg Subtype.val he)),by
    rintro ⟨x,hx⟩
    obtain ⟨y,rfl⟩ := finSumFinEquiv.surjective x
    cases y with
    | inl i => exact ⟨i,rfl⟩
    | inr j => simp [pattern] at hx⟩

def rightFiber (h d : ℕ) : Fin d ≃ {i : Fin (h+d) // pattern h d i = 1} :=
  Equiv.ofBijective (fun i => ⟨right i,pattern_right h d i⟩) ⟨by
    intro i j he
    exact Sum.inr.inj (finSumFinEquiv.injective (congrArg Subtype.val he)),by
    rintro ⟨x,hx⟩
    obtain ⟨y,rfl⟩ := finSumFinEquiv.surjective x
    cases y with
    | inl i => simp [pattern] at hx
    | inr j => exact ⟨j,rfl⟩⟩

def leftPerm {h d : ℕ} (p : Equiv.Perm (Fin (h+d))) (hp : pattern h d ∘ p = pattern h d) :
    Equiv.Perm (Fin h) :=
  (leftFiber h d).trans ((p.subtypePerm (fun i => by have hi : pattern h d (p i) = pattern h d i := congrFun hp i; rw [hi])).trans (leftFiber h d).symm)

def rightPerm {h d : ℕ} (p : Equiv.Perm (Fin (h+d))) (hp : pattern h d ∘ p = pattern h d) :
    Equiv.Perm (Fin d) :=
  (rightFiber h d).trans ((p.subtypePerm (fun i => by have hi : pattern h d (p i) = pattern h d i := congrFun hp i; rw [hi])).trans (rightFiber h d).symm)

theorem perm_left {h d : ℕ} (p : Equiv.Perm (Fin (h+d)))
    (hp : pattern h d ∘ p = pattern h d) (i : Fin h) : p (left i) = left (leftPerm p hp i) := by
  have he := congrArg Subtype.val ((leftFiber h d).apply_symm_apply
    ((p.subtypePerm (fun i => by have hi : pattern h d (p i) = pattern h d i := congrFun hp i; rw [hi])) (leftFiber h d i)))
  exact he.symm

theorem perm_right {h d : ℕ} (p : Equiv.Perm (Fin (h+d)))
    (hp : pattern h d ∘ p = pattern h d) (i : Fin d) : p (right i) = right (rightPerm p hp i) := by
  have he := congrArg Subtype.val ((rightFiber h d).apply_symm_apply
    ((p.subtypePerm (fun i => by have hi : pattern h d (p i) = pattern h d i := congrFun hp i; rw [hi])) (rightFiber h d i)))
  exact he.symm

theorem block_preserves {h d : ℕ} (p : Equiv.Perm (Fin h)) (q : Equiv.Perm (Fin d)) :
    pattern h d ∘ SymmetricPowerOperations.blockPerm p q = pattern h d := by
  funext i
  obtain ⟨s,rfl⟩ := finSumFinEquiv.surjective i
  cases s <;> simp [pattern,SymmetricPowerOperations.blockPerm]

theorem stabilizer_decomposition {h d : ℕ} (p : Equiv.Perm (Fin (h+d)))
    (hp : pattern h d ∘ p = pattern h d) :
    p = SymmetricPowerOperations.blockPerm (leftPerm p hp) (rightPerm p hp) := by
  apply Equiv.ext
  intro i
  obtain ⟨s,rfl⟩ := finSumFinEquiv.surjective i
  cases s with
  | inl i => simpa [left,SymmetricPowerOperations.blockPerm] using perm_left p hp i
  | inr i => simpa [right,SymmetricPowerOperations.blockPerm] using perm_right p hp i

theorem count_left (h d : ℕ) : (Finset.univ.filter (fun i => pattern h d i = 0)).card = h := by
  simpa only [Fintype.card_fin,Fintype.card_subtype] using (Fintype.card_congr (leftFiber h d)).symm

theorem count_right (h d : ℕ) : (Finset.univ.filter (fun i => pattern h d i = 1)).card = d := by
  simpa only [Fintype.card_fin,Fintype.card_subtype] using (Fintype.card_congr (rightFiber h d)).symm

theorem orbit_iff_counts (h d : ℕ) (labels : Fin (h+d) → Fin 2) :
    TypedSymmetricPatternHom.Orbit (pattern h d) labels ↔
      (Finset.univ.filter (fun i => labels i = 0)).card = h ∧
      (Finset.univ.filter (fun i => labels i = 1)).card = d := by
  constructor
  · rintro ⟨p,hp⟩
    have hc (s : Fin 2) : (Finset.univ.filter (fun i => labels i = s)).card =
        (Finset.univ.filter (fun i => pattern h d i = s)).card := by
      let e : {i // pattern h d i = s} ≃ {i // labels i = s} :=
        p.subtypeEquiv (by intro i; have hi : labels (p i) = pattern h d i := congrFun hp i; rw [hi])
      simpa only [Fintype.card_subtype] using (Fintype.card_congr e).symm
    exact ⟨(hc 0).trans (count_left h d),(hc 1).trans (count_right h d)⟩
  · rintro ⟨h0,h1⟩
    apply FiniteSpeciesExterior.permutation_of_counts
    intro s
    fin_cases s
    · change (Finset.univ.filter (fun i => labels i = 0)).card =
        (Finset.univ.filter (fun i => pattern h d i = 0)).card
      rw [count_left]; exact h0
    · change (Finset.univ.filter (fun i => labels i = 1)).card =
        (Finset.univ.filter (fun i => pattern h d i = 1)).card
      rw [count_right]; exact h1

end
end Math.TwoSpeciesPattern
