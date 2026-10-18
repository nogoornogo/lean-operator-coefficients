import GUT.SUN.Matching.TreeMatching
import GUT.SU6.Matching.TreeMatching

open Math

/-! Specializations and degeneracy controls for the uniform matching theorem.
These compare the existing coefficients, not only their nonzero propositions. -/
set_option autoImplicit false
namespace GUT.SUN.MatchingControls

noncomputable section
open DiagonalBackground

def fixedDiagonal (r : ℕ) (v : ℝ) (i : Fin (5+r)) : ℝ :=
  if i.val < 3 then 2*v else if i.val < 5 then -3*v else 0

def fixed (r : ℕ) (v : ℝ) (hv : v ≠ 0) : Background r where
  a := 2*v
  b := -3*v
  diagonal := fixedDiagonal r v
  color i := by simp [fixedDiagonal, colorIndex]
  weak i := by
    have h : ¬3 + i.val < 3 := by omega
    have h5 : 3 + i.val < 5 := by omega
    simp [fixedDiagonal, weakIndex, h, h5]
  trace_zero := by
    have h : ∀ i : Fin r, ¬5 + i.val < 3 := by intro i; omega
    simp [fixedDiagonal, Fin.sum_univ_add, Fin.sum_univ_succ, h]
    ring
  separated := by intro h; apply hv; linarith

theorem fixed_effectiveV (r : ℕ) (v : ℝ) (hv : v ≠ 0) :
    (fixed r v hv).effectiveV = v := by
  simp only [Background.effectiveV, fixed]
  ring

theorem fixed_coefficient (r : ℕ) (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    TreeMatching.coefficient (fixed r v hv) g hg =
      SU5.MediatorMatching.coefficient g v hg hv := by
  simpa only [fixed_effectiveV] using TreeMatching.coefficient_eq (fixed r v hv) g hg
theorem fixed_generated (r : ℕ) (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    TreeMatching.generated (fixed r v hv) g hg =
      SU5.MediatorMatching.generated g v hg hv := by
  simpa only [fixed_effectiveV] using TreeMatching.generated_eq (fixed r v hv) g hg

theorem su5_coefficient (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    TreeMatching.coefficient (fixed 0 v hv) g hg =
      SU5.MediatorMatching.coefficient g v hg hv :=
  fixed_coefficient 0 g v hg hv
theorem su6_coefficient (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    TreeMatching.coefficient (fixed 1 v hv) g hg =
      SU6.TreeMatching.coefficient g v hg hv := by
  rw [fixed_coefficient, SU6.TreeMatching.coefficient_eq]
theorem su6_generated (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    TreeMatching.generated (fixed 1 v hv) g hg =
      SU6.TreeMatching.generated g v hg hv := by
  rw [fixed_generated, SU6.TreeMatching.generated_eq]

theorem su6_embed : ExteriorSquareBlock.embed 1 = SU6.ExteriorCurrents.embedTen := rfl
theorem su6_project : ExteriorSquareBlock.project 1 = SU6.ExteriorCurrents.projectTen := rfl
theorem su6_background (v : ℝ) (hv : v ≠ 0) :
    (fixed 1 v hv).matrix = SU6.AdjointMass.background v := by
  unfold Background.matrix SU6.AdjointMass.background
  congr 1
  ext i
  fin_cases i <;> simp [fixed, fixedDiagonal, SU6.AdjointMass.diagonal, SU6.AdjointMass.weight]

def su6_extra (v : ℝ) (hv : v ≠ 0) (i : Fin 5) : (fixed 1 v hv).ExtraRoot :=
  ⟨(i.castSucc,5), by
    refine ⟨i.isLt, by norm_num, ?_⟩
    fin_cases i <;> simp [fixed, fixedDiagonal, hv]⟩

theorem su6_extra_bijective (v : ℝ) (hv : v ≠ 0) : Function.Bijective (su6_extra v hv) := by
  constructor
  · intro i j h
    have h' := congrArg (fun x => x.val.1.val) h
    exact Fin.ext h'
  · intro c
    have hj : c.val.2.val = 5 := by have := c.property.2.1; have := c.val.2.isLt; omega
    have hi : c.val.1.val < 5 := by have := c.property.1; change c.val.1.val < c.val.2.val at this; omega
    refine ⟨⟨c.val.1.val,hi⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext; exact hj.symm

theorem su6_extra_mass (g v : ℝ) (hv : v ≠ 0) (i : Fin 5) :
    (fixed 1 v hv).massSquared g (.inr (su6_extra v hv i)) =
      SU6.AdjointMass.massSquared g v (.inr i) := by
  fin_cases i <;>
    simp [Background.massSquared, Background.first, Background.second, su6_extra,
      fixed, fixedDiagonal, SU6.AdjointMass.massSquared] <;> ring
theorem su6_extra_up (v : ℝ) (hv : v ≠ 0) (i : Fin 5) :
    ExteriorCurrents.upCurrent (fixed 1 v hv) (.inr (su6_extra v hv i)) =
      SU6.ExteriorCurrents.upCurrent (.inr i) := by
  rw [ExteriorCurrents.upCurrent_extra, SU6.ExteriorCurrents.upCurrent_extra]
theorem su6_extra_electron (v : ℝ) (hv : v ≠ 0) (i : Fin 5) :
    ExteriorCurrents.electronCurrent (fixed 1 v hv) (.inr (su6_extra v hv i)) =
      SU6.ExteriorCurrents.electronCurrent (.inr i) := by
  rw [ExteriorCurrents.electronCurrent_extra, SU6.ExteriorCurrents.electronCurrent_extra]

def su7 (t : ℝ) : Background 2 where
  a := 2
  b := -3
  diagonal := ![2,2,2,-3,-3,t,-t]
  color i := by fin_cases i <;> rfl
  weak i := by fin_cases i <;> rfl
  trace_zero := by simp [Fin.sum_univ_succ]; ring
  separated := by norm_num

theorem su7_equal_spectators : (su7 0).diagonal 5 = (su7 0).diagonal 6 := by
  change (0 : ℝ) = -0
  ring
def su7_extra_pair : (su7 1).ExtraRoot :=
  ⟨(5,6), by
    refine ⟨by decide, by decide, ?_⟩
    change (1 : ℝ) ≠ -1
    norm_num⟩
theorem su7_extra_pair_mass (g : ℝ) :
    (su7 1).massSquared g (.inr su7_extra_pair) = 4*g^2 := by
  change g^2 * (1 - -1)^2 = 4*g^2
  ring
theorem su7_extra_pair_currents :
    ExteriorCurrents.upCurrent (su7 1) (.inr su7_extra_pair) = 0 ∧
      ExteriorCurrents.electronCurrent (su7 1) (.inr su7_extra_pair) = 0 :=
  ⟨ExteriorCurrents.upCurrent_extra _ _, ExteriorCurrents.electronCurrent_extra _ _⟩
theorem su7_collision_with_core : (su7 2).diagonal 0 = (su7 2).diagonal 5 := rfl
theorem su7_generated (t g : ℝ) (hg : g ≠ 0) :
    TreeMatching.generated (su7 t) g hg = SU5.MediatorMatching.generated g 1 hg one_ne_zero := by
  have h : (su7 t).effectiveV = 1 := by norm_num [Background.effectiveV, su7]
  simpa only [h] using TreeMatching.generated_eq (su7 t) g hg
theorem su7_generated_nonzero (t g : ℝ) (hg : g ≠ 0) :
    TreeMatching.generated (su7 t) g hg ≠ 0 :=
  TreeMatching.generated_nonzero _ _ hg

end
end GUT.SUN.MatchingControls
