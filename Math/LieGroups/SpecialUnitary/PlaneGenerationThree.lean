import Math.RepresentationTheory.Invariants.GeneratorInvariantTests
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Algebraic generation of actual SU(3) by coordinate-plane unitary matrices. -/
namespace Math.SU3PlaneGeneration
noncomputable section
open Matrix
abbrev SU3 := specialUnitaryGroup (Fin 3) ℂ

/-- Actual plane matrices: one coordinate basis vector is fixed. -/
def planes : Set SU3 := {g | ∃ i : Fin 3, ∀ j, g.val j i = if j = i then 1 else 0}

def matrix01 (a b : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![a, b, 0; -star b, star a, 0; 0, 0, 1]
def matrix02 (a b : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![a, 0, b; 0, 1, 0; -star b, 0, star a]

theorem matrix01_mem (a b : ℂ) (h : a * star a + b * star b = 1) :
    matrix01 a b ∈ specialUnitaryGroup (Fin 3) ℂ := by
  simp only [Complex.star_def] at h
  rw [mem_specialUnitaryGroup_iff]
  constructor
  · rw [mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix01, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      first | (solve | ring) | (solve | linear_combination h)
  · simp [matrix01, Matrix.det_fin_three]
    linear_combination h

theorem matrix02_mem (a b : ℂ) (h : a * star a + b * star b = 1) :
    matrix02 a b ∈ specialUnitaryGroup (Fin 3) ℂ := by
  simp only [Complex.star_def] at h
  rw [mem_specialUnitaryGroup_iff]
  constructor
  · rw [mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix02, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      first | (solve | ring) | (solve | linear_combination h)
  · simp [matrix02, Matrix.det_fin_three]
    linear_combination h

def rotation01 (a b : ℂ) (h : a * star a + b * star b = 1) : SU3 :=
  ⟨matrix01 a b, matrix01_mem a b h⟩
def rotation02 (a b : ℂ) (h : a * star a + b * star b = 1) : SU3 :=
  ⟨matrix02 a b, matrix02_mem a b h⟩

theorem rotation01_plane (a b : ℂ) (h) : rotation01 a b h ∈ planes := by
  refine ⟨2, ?_⟩
  intro j
  fin_cases j <;> simp [rotation01, matrix01]
theorem rotation02_plane (a b : ℂ) (h) : rotation02 a b h ∈ planes := by
  refine ⟨1, ?_⟩
  intro j
  fin_cases j <;> simp [rotation02, matrix02]

/-- A normalized actual rotation annihilates the second coordinate of any pair. -/
theorem eliminate_pair (x y : ℂ) :
    ∃ a b : ℂ, a * star a + b * star b = 1 ∧ -star b * x + star a * y = 0 := by
  by_cases hz : x = 0 ∧ y = 0
  · exact ⟨1, 0, by simp, by simp [hz.1, hz.2]⟩
  let r : ℝ := Real.sqrt (Complex.normSq x + Complex.normSq y)
  have hs : 0 < Complex.normSq x + Complex.normSq y := by
    have hx := Complex.normSq_nonneg x
    have hy := Complex.normSq_nonneg y
    have hn : Complex.normSq x + Complex.normSq y ≠ 0 := by
      intro he
      apply hz
      constructor <;> apply Complex.normSq_eq_zero.mp <;> linarith
    exact lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hn)
  have hr : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hr2 : (r : ℂ) ^ 2 = (Complex.normSq x : ℂ) + (Complex.normSq y : ℂ) := by
    exact_mod_cast Real.sq_sqrt (le_of_lt hs)
  refine ⟨star x / r, star y / r, ?_, ?_⟩
  · simp only [Complex.star_def, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    rw [div_mul_div_comm, div_mul_div_comm, ← add_div]
    have hn : starRingEnd ℂ x * x + starRingEnd ℂ y * y =
        (Complex.normSq x : ℂ) + (Complex.normSq y : ℂ) := by
      rw [mul_comm (starRingEnd ℂ x) x, mul_comm (starRingEnd ℂ y) y,
        Complex.mul_conj, Complex.mul_conj]
    rw [hn, ← hr2]
    field_simp
  · simp only [Complex.star_def, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    ring

theorem column_norm (g : SU3) :
    star (g.val 0 0) * g.val 0 0 + star (g.val 1 0) * g.val 1 0 +
      star (g.val 2 0) * g.val 2 0 = 1 := by
  have hu := (mem_specialUnitaryGroup_iff.mp g.property).1
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0)
    (mem_unitaryGroup_iff'.mp hu)
  simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply, add_assoc] using he

/-- Two actual plane rotations move the first column to the first basis vector. -/
theorem reduce_first_column (g : SU3) :
    ∃ p q : SU3, p ∈ planes ∧ q ∈ planes ∧
      ∀ j : Fin 3, (q * p * g).val j 0 = if j = 0 then 1 else 0 := by
  obtain ⟨a, b, hn, hz⟩ := eliminate_pair (g.val 0 0) (g.val 1 0)
  let p := rotation01 a b hn
  let u := p * g
  have hu1 : u.val 1 0 = 0 := by
    change (matrix01 a b * g.val) 1 0 = 0
    simpa [matrix01, Matrix.mul_apply, Fin.sum_univ_succ] using hz
  have hu : star (u.val 0 0) * u.val 0 0 + star (u.val 2 0) * u.val 2 0 = 1 := by
    simpa [hu1] using column_norm u
  let q := rotation02 (star (u.val 0 0)) (star (u.val 2 0)) (by simpa using hu)
  refine ⟨p, q, rotation01_plane a b hn, rotation02_plane _ _ _, ?_⟩
  intro j
  rw [mul_assoc]
  change (q * u).val j 0 = _
  change (matrix02 (star (u.val 0 0)) (star (u.val 2 0)) * u.val) j 0 = _
  fin_cases j
  · simpa [matrix02, Matrix.mul_apply, Fin.sum_univ_succ] using hu
  · simp [matrix02, Matrix.mul_apply, Fin.sum_univ_succ, hu1]
  · simp [matrix02, Matrix.mul_apply, Fin.sum_univ_succ]
    ring

/-- Unitarity turns a fixed coordinate column into a fixed coordinate row. -/
theorem row_fixed (g : SU3) (i : Fin 3)
    (hv : ∀ j, g.val j i = if j = i then 1 else 0) :
    ∀ j, g.val i j = if j = i then 1 else 0 := by
  intro j
  have hu := (mem_specialUnitaryGroup_iff.mp g.property).1
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M j i)
    (mem_unitaryGroup_iff'.mp hu)
  have hs : star (g.val i j) = if j = i then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, hv] using he
  simpa using congrArg star hs

def tailMatrix (g : SU3) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![g.val 1 1, g.val 1 2; g.val 2 1, g.val 2 2]

/-- The remaining block is an actual SU(2) element, not just an invertible block. -/
theorem tail_mem (g : SU3)
    (hv : ∀ j, g.val j 0 = if j = 0 then 1 else 0) :
    tailMatrix g ∈ specialUnitaryGroup (Fin 2) ℂ := by
  have hr := row_fixed g 0 hv
  obtain ⟨hu, hd⟩ := mem_specialUnitaryGroup_iff.mp g.property
  have he := mem_unitaryGroup_iff.mp hu
  rw [mem_specialUnitaryGroup_iff]
  constructor
  · rw [mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [tailMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    · simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply, hv] using
        congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 1 1) he
    · simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply, hv] using
        congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 1 2) he
    · simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply, hv] using
        congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 2 1) he
    · simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply, hv] using
        congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 2 2) he
  · simpa [tailMatrix, Matrix.det_fin_two, Matrix.det_fin_three, hv, hr] using hd

theorem inverse_plane {g : SU3} (hg : g ∈ planes) : g⁻¹ ∈ planes := by
  obtain ⟨i, hi⟩ := hg
  refine ⟨i, ?_⟩
  intro j
  change star (g.val i j) = if j = i then 1 else 0
  rw [row_fixed g i hi j]
  split <;> simp

/-- Every actual SU(3) element is a product of three actual plane elements. -/
theorem three_plane_decomposition (g : SU3) :
    ∃ a b c : SU3, a ∈ planes ∧ b ∈ planes ∧ c ∈ planes ∧ g = a * b * c := by
  obtain ⟨p, q, hp, hq, hv⟩ := reduce_first_column g
  refine ⟨p⁻¹, q⁻¹, q * p * g, inverse_plane hp, inverse_plane hq, ⟨0, hv⟩, ?_⟩
  simp [mul_assoc]

/-- Algebraic (not topological) closure of actual plane matrices is all SU(3). -/
theorem closure_planes : Subgroup.closure planes = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨p, q, hp, hq, hv⟩ := reduce_first_column g
  have hr : q * p * g ∈ planes := ⟨0, hv⟩
  have hp' := Subgroup.subset_closure hp
  have hq' := Subgroup.subset_closure hq
  have hr' := Subgroup.subset_closure hr
  have he : g = (q * p)⁻¹ * (q * p * g) := by simp [mul_assoc]
  rw [he]
  exact (Subgroup.closure planes).mul_mem
    ((Subgroup.closure planes).inv_mem ((Subgroup.closure planes).mul_mem hq' hp')) hr'

/-- A family of actual group elements, with its infinite SU(2) parameters retained. -/
def generator (p : planes) : SU3 := p.val

theorem generates : Subgroup.closure (Set.range generator) = ⊤ := by
  have he : Set.range generator = planes := by
    ext g
    exact ⟨fun ⟨p, hp⟩ => hp ▸ p.property, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩
  rw [he]
  exact closure_planes

theorem invariant_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU3 V) (f : Module.Dual ℂ V) :
    (∀ g v, f (rho g v) = f v) ↔ (∀ p v, f (rho (generator p) v) = f v) :=
  Math.GeneratorInvariantTests.invariant_iff rho generator generates f

end
end Math.SU3PlaneGeneration
