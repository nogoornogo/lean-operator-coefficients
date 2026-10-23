import Math.RepresentationTheory.Exterior.ExteriorSquareBlock
import GUT.SU5.Matching.AdjointMass

open Math

/-! A real diagonal background with an unbroken color/weak block.
Only unequal-weight root pairs enter the massive mediator sector. -/
set_option autoImplicit false
namespace GUT.SUN.DiagonalBackground

noncomputable section
open scoped Matrix

def colorIndex (r : ℕ) (i : Fin 3) : Fin (5+r) := ⟨i.val, by omega⟩
def weakIndex (r : ℕ) (i : Fin 2) : Fin (5+r) := ⟨3+i.val, by omega⟩

structure Background (r : ℕ) where
  a : ℝ
  b : ℝ
  diagonal : Fin (5+r) → ℝ
  color : ∀ i, diagonal (colorIndex r i) = a
  weak : ∀ i, diagonal (weakIndex r i) = b
  trace_zero : ∑ i, diagonal i = 0
  separated : a ≠ b

namespace Background
variable {r : ℕ} (D : Background r)

def matrix : Matrix (Fin (5+r)) (Fin (5+r)) ℂ :=
  Matrix.diagonal fun i => (D.diagonal i : ℂ)

theorem matrix_trace : Matrix.trace D.matrix = 0 := by
  simpa [matrix, Matrix.trace] using congrArg (fun x : ℝ => (x : ℂ)) D.trace_zero

theorem matrix_hermitian : D.matrixᴴ = D.matrix := by
  ext i j
  by_cases h : i = j
  · subst j; simp [matrix, Matrix.conjTranspose_apply]
  · simp [matrix, Matrix.conjTranspose_apply, h, Ne.symm h]

def effectiveV : ℝ := (D.a - D.b) / 5
theorem effectiveV_ne_zero : D.effectiveV ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr D.separated) (by norm_num)

def ExtraRoot := {ij : Fin (5+r) × Fin (5+r) //
  ij.1 < ij.2 ∧ 5 ≤ ij.2.val ∧ D.diagonal ij.1 ≠ D.diagonal ij.2}
instance : Fintype D.ExtraRoot := by classical exact Subtype.fintype _

abbrev Channel := (Fin 3 × Fin 2) ⊕ D.ExtraRoot
def first : D.Channel → Fin (5+r)
  | .inl iw => colorIndex r iw.1
  | .inr ij => ij.val.1
def second : D.Channel → Fin (5+r)
  | .inl iw => weakIndex r iw.2
  | .inr ij => ij.val.2
def upper (c : D.Channel) := Matrix.single (D.first c) (D.second c) (1 : ℂ)
def lower (c : D.Channel) := Matrix.single (D.second c) (D.first c) (1 : ℂ)

theorem ordered (c : D.Channel) : D.first c < D.second c := by
  cases c with
  | inl iw => simp only [first, second, colorIndex, weakIndex, Fin.mk_lt_mk]; omega
  | inr ij => exact ij.property.1

theorem unequal (c : D.Channel) : D.diagonal (D.first c) ≠ D.diagonal (D.second c) := by
  cases c with
  | inl iw => simpa only [first, second, D.color, D.weak] using D.separated
  | inr ij => exact ij.property.2.2

theorem covers (i j : Fin (5+r)) (hij : i < j) (hne : D.diagonal i ≠ D.diagonal j) :
    ∃ c : D.Channel, D.first c = i ∧ D.second c = j := by
  by_cases hj : 5 ≤ j.val
  · exact ⟨.inr ⟨(i,j), hij, hj, hne⟩, rfl, rfl⟩
  · have hi : i.val < 3 := by
      by_contra hc
      have ei : i = weakIndex r ⟨i.val-3, by omega⟩ := by apply Fin.ext; simp [weakIndex]; omega
      have ej : j = weakIndex r ⟨j.val-3, by omega⟩ := by apply Fin.ext; simp [weakIndex]; omega
      exact hne ((congrArg D.diagonal ei).trans ((D.weak _).trans
        ((D.weak _).symm.trans (congrArg D.diagonal ej).symm)))
    have hj3 : 3 ≤ j.val := by
      by_contra hc
      have ei : i = colorIndex r ⟨i.val, hi⟩ := rfl
      have ej : j = colorIndex r ⟨j.val, by omega⟩ := rfl
      exact hne ((congrArg D.diagonal ei).trans ((D.color _).trans
        ((D.color _).symm.trans (congrArg D.diagonal ej).symm)))
    refine ⟨.inl (⟨i.val, hi⟩, ⟨j.val-3, by omega⟩), rfl, ?_⟩
    apply Fin.ext
    simp [second, weakIndex]
    omega

theorem channel_injective : Function.Injective (fun c : D.Channel => (D.first c, D.second c)) := by
  intro x y h
  have h1 := congrArg (fun z => z.1.val) h
  have h2 := congrArg (fun z => z.2.val) h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      congr 1
      apply Prod.ext <;> apply Fin.ext
      · exact h1
      · simpa [second, weakIndex] using h2
    | inr y =>
      have := y.property.2.1
      simp [second, weakIndex] at h2
      omega
  | inr x =>
    cases y with
    | inl y =>
      have := x.property.2.1
      simp [second, weakIndex] at h2
      omega
    | inr y =>
      congr 1
      apply Subtype.ext
      exact h

def massSquared (g : ℝ) (c : D.Channel) : ℝ :=
  g^2 * (D.diagonal (D.first c) - D.diagonal (D.second c))^2
def massOperator (g : ℝ) (X : Matrix (Fin (5+r)) (Fin (5+r)) ℂ) :=
  (g : ℂ)^2 • DiagonalAdjointMass.operator (fun i => (D.diagonal i : ℂ)) X

theorem upper_mass (g : ℝ) (c : D.Channel) :
    D.massOperator g (D.upper c) = (D.massSquared g c : ℂ) • D.upper c := by
  simp [massOperator, upper, DiagonalAdjointMass.single_eigenvector, massSquared]
theorem lower_mass (g : ℝ) (c : D.Channel) :
    D.massOperator g (D.lower c) = (D.massSquared g c : ℂ) • D.lower c := by
  simp [massOperator, lower, DiagonalAdjointMass.single_eigenvector, massSquared,
    sub_sq_comm]
theorem massSquared_pos (g : ℝ) (hg : g ≠ 0) (c : D.Channel) :
    0 < D.massSquared g c :=
  mul_pos (sq_pos_of_ne_zero hg) (sq_pos_of_ne_zero (sub_ne_zero.mpr (D.unequal c)))
theorem massSquared_ne_zero (g : ℝ) (hg : g ≠ 0) (c : D.Channel) :
    (D.massSquared g c : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (D.massSquared_pos g hg c)
theorem core_mass (g : ℝ) (i : Fin 3) (w : Fin 2) :
    D.massSquared g (.inl (i,w)) = SU5.AdjointMass.massSquared g D.effectiveV := by
  simp only [massSquared, first, second, D.color, D.weak, SU5.AdjointMass.massSquared, effectiveV]
  ring
theorem equal_weight_entry_zero (g : ℝ) (X : Matrix (Fin (5+r)) (Fin (5+r)) ℂ)
    (i j : Fin (5+r)) (h : D.diagonal i = D.diagonal j) :
    D.massOperator g X i j = 0 := by
  simp [massOperator, DiagonalAdjointMass.entry, h]

end Background
end
end GUT.SUN.DiagonalBackground
