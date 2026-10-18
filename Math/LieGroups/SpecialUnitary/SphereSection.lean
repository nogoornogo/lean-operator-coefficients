import Math.Topology.SpecialUnitaryConnected
import Math.LieGroups.SpecialUnitary.VectorStabilizer
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Explicit local sections of the last-column map. The sphere carries
its Euclidean topology, not the coordinate sup-norm sphere. -/

set_option autoImplicit false

namespace Math.SUN.SphereSection

noncomputable section

open Matrix
open scoped ComplexConjugate

def rankOne {ι : Type*} (v : ι → ℂ) : Matrix ι ι ℂ := vecMulVec v (star v)

theorem rankOne_star {ι : Type*} (v : ι → ℂ) : star (rankOne v) = rankOne v := by
  simp [rankOne, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_vecMulVec]

theorem rankOne_sq {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    rankOne v * rankOne v = (star v ⬝ᵥ v) • rankOne v := by
  simp [rankOne, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]

/-- A complex rank-one modification, with a denominator avoiding zero. -/
theorem rankOne_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℂ) (c : ℂ) (hc : c ≠ 0) (hv : star v ⬝ᵥ v = c + star c) :
    -1 + c⁻¹ • rankOne v ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [star_add, star_neg, star_one, star_smul, star_inv₀, rankOne_star,
    mul_add, add_mul, neg_mul, mul_neg, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, rankOne_sq, hv, smul_smul]
  have hs : star c ≠ 0 := star_ne_zero.mpr hc
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

abbrev Space (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev Sphere (n : ℕ) := Metric.sphere (0 : Space n) 1

theorem sphere_dot {n : ℕ} (v : Sphere n) : star (v.val : Fin n → ℂ) ⬝ᵥ v.val = 1 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
  have hv : ‖v.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  simp [hv]

def pole (n : ℕ) : Fin (n + 1) → ℂ := VectorStabilizer.lastVector n

def denominator {n : ℕ} (v : Sphere (n + 1)) : ℂ := 1 + star (v.val (Fin.last n))

def vector {n : ℕ} (v : Sphere (n + 1)) : Fin (n + 1) → ℂ := pole n + v.val

theorem vector_dot {n : ℕ} (v : Sphere (n + 1)) :
    star (vector v) ⬝ᵥ vector v = denominator v + star (denominator v) := by
  simp only [vector, star_add, dotProduct_add, add_dotProduct]
  rw [sphere_dot]
  simp [pole, VectorStabilizer.lastVector, denominator, dotProduct_single,
    single_dotProduct, add_comm, add_left_comm, add_assoc]

def patch (n : ℕ) : Set (Sphere (n + 1)) := {v | denominator v ≠ 0}

def unitarySection {n : ℕ} (v : patch n) : SpecialUnitaryTopology.Unitary (n + 1) :=
  ⟨-1 + (denominator v.val)⁻¹ • rankOne (vector v.val),
    rankOne_unitary _ _ v.property (vector_dot v.val)⟩

theorem unitarySection_last_column {n : ℕ} (v : patch n) (i : Fin (n + 1)) :
    (unitarySection v).val i (Fin.last n) = v.val.val i := by
  have hq : star (vector v.val) (Fin.last n) = denominator v.val := by
    simp [vector, pole, VectorStabilizer.lastVector, denominator]
  change -(1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i (Fin.last n) +
    (denominator v.val)⁻¹ * (vector v.val i * star (vector v.val) (Fin.last n)) = _
  rw [hq]
  have hc : denominator v.val ≠ 0 := v.property
  simp only [Matrix.one_apply, vector, Pi.add_apply, pole, VectorStabilizer.lastVector,
    Pi.single_apply]
  split_ifs <;> field_simp <;> ring

theorem denominator_continuous (n : ℕ) : Continuous (@denominator n) := by
  unfold denominator
  fun_prop

theorem patch_isOpen (n : ℕ) : IsOpen (patch n) :=
  isOpen_ne.preimage (denominator_continuous n)

def north (n : ℕ) : Sphere (n + 1) :=
  ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩

theorem north_mem_patch (n : ℕ) : north n ∈ patch n := by
  simp [patch, denominator, north]

theorem unitarySection_continuous (n : ℕ) : Continuous (@unitarySection n) := by
  apply continuous_induced_rng.mpr
  have hc : Continuous (fun v : patch n => (denominator v.val)⁻¹) :=
    ((denominator_continuous n).comp continuous_subtype_val).inv₀ (fun v => v.property)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun v : patch n =>
    -(1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j +
      (denominator v.val)⁻¹ * (vector v.val i * star (vector v.val j)))
  unfold vector
  fun_prop

/-- Correction on the right preserves the last column when the rank is at least two. -/
def correctRight {n : ℕ} (g : SpecialUnitaryTopology.Unitary (n + 2)) : Block.Group (n + 2) :=
  ⟨g.val * SpecialUnitaryTopology.correction g,
    (Matrix.unitaryGroup _ ℂ).mul_mem g.property
      (SpecialUnitaryTopology.correction_unitary _), by
      change Matrix.det (g.val * SpecialUnitaryTopology.correction g) = 1
      rw [Matrix.det_mul, SpecialUnitaryTopology.correction_det]
      exact (Matrix.det_of_mem_unitary g.property).2⟩

theorem correctRight_last_column {n : ℕ} (g : SpecialUnitaryTopology.Unitary (n + 2))
    (i : Fin (n + 2)) : (correctRight g).val i (Fin.last (n + 1)) = g.val i (Fin.last (n + 1)) := by
  change (g.val * SpecialUnitaryTopology.correction g) i (Fin.last (n + 1)) = _
  have hlast : Fin.last (n + 1) ≠ (0 : Fin (n + 2)) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  simp [SpecialUnitaryTopology.correction, Matrix.mul_diagonal, hlast]

theorem correctRight_continuous (n : ℕ) : Continuous (@correctRight n) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun g : SpecialUnitaryTopology.Unitary (n + 2) =>
    g.val * SpecialUnitaryTopology.correction g)
  apply Continuous.mul continuous_subtype_val
  apply Continuous.matrix_diagonal
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · simp only [hi, ite_true]
    exact (continuous_subtype_val.matrix_det).star
  · simp only [hi, ite_false]
    exact continuous_const

def specialSection {n : ℕ} (v : patch (n + 1)) : Block.Group (n + 2) :=
  correctRight (unitarySection v)

theorem specialSection_last_column {n : ℕ} (v : patch (n + 1)) (i : Fin (n + 2)) :
    (specialSection v).val i (Fin.last (n + 1)) = v.val.val i := by
  rw [specialSection, correctRight_last_column, unitarySection_last_column]

theorem specialSection_continuous (n : ℕ) : Continuous (@specialSection n) :=
  (correctRight_continuous n).comp (unitarySection_continuous (n + 1))

def columnVector {n : ℕ} (g : Block.Group (n + 1)) : Space (n + 1) :=
  WithLp.toLp 2 (fun i => g.val i (Fin.last n))

theorem columnVector_norm {n : ℕ} (g : Block.Group (n + 1)) : ‖columnVector g‖ = 1 := by
  have hd : star (columnVector g : Fin (n + 1) → ℂ) ⬝ᵥ columnVector g = 1 := by
    have h := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ =>
      A (Fin.last n) (Fin.last n)) g.property.1.1
    simpa [columnVector, dotProduct, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply] using h
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K] at hd
  change (Complex.ofReal ‖columnVector g‖) ^ 2 = 1 at hd
  have hr : ‖columnVector g‖ ^ 2 = 1 := by
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] using
      congrArg Complex.re hd
  nlinarith [norm_nonneg (columnVector g)]

def projection {n : ℕ} (g : Block.Group (n + 1)) : Sphere (n + 1) :=
  ⟨columnVector g, mem_sphere_zero_iff_norm.mpr (columnVector_norm g)⟩

theorem projection_continuous (n : ℕ) : Continuous (@projection n) := by
  apply continuous_induced_rng.mpr
  change Continuous (@columnVector n)
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  exact (continuous_apply (Fin.last n)).comp ((continuous_apply i).comp continuous_subtype_val)

theorem projection_specialSection {n : ℕ} (v : patch (n + 1)) :
    projection (specialSection v) = v.val := by
  apply Subtype.ext
  ext i
  exact specialSection_last_column v i

theorem mulVec_pole {n : ℕ} (g : Block.Group (n + 1)) :
    g.val *ᵥ pole n = (projection g).val := by
  simp [pole, VectorStabilizer.lastVector, Matrix.mulVec_single, projection, columnVector,
    Matrix.col]
  rfl

theorem projection_mul_stabilizer {n : ℕ} (g : Block.Group (n + 1))
    (h : VectorStabilizer.subgroup n) : projection (g * h.val) = projection g := by
  apply Subtype.ext
  apply WithLp.ofLp_injective
  rw [← mulVec_pole, ← mulVec_pole]
  change (g.val * h.val.val) *ᵥ pole n = _
  rw [← Matrix.mulVec_mulVec]
  exact congrArg (fun v => g.val *ᵥ v) h.property

theorem difference_mem_stabilizer {n : ℕ} (g h : Block.Group (n + 1))
    (hh : projection g = projection h) : g⁻¹ * h ∈ VectorStabilizer.subgroup n := by
  change (g⁻¹.val * h.val) *ᵥ pole n = pole n
  rw [← Matrix.mulVec_mulVec, mulVec_pole, ← hh, ← mulVec_pole, Matrix.mulVec_mulVec]
  have hi : g⁻¹.val * g.val = 1 := g.property.1.1
  rw [hi, Matrix.one_mulVec]

def antipode {n : ℕ} (v : Sphere n) : Sphere n :=
  ⟨-v.val, by simp⟩

theorem antipode_continuous (n : ℕ) : Continuous (@antipode n) :=
  continuous_induced_rng.mpr continuous_subtype_val.neg

theorem antipode_antipode {n : ℕ} (v : Sphere n) : antipode (antipode v) = v := by
  apply Subtype.ext
  exact neg_neg _

def southPatch (n : ℕ) : Set (Sphere (n + 1)) := antipode ⁻¹' patch n

theorem southPatch_isOpen (n : ℕ) : IsOpen (southPatch n) :=
  (patch_isOpen n).preimage (antipode_continuous (n + 1))

theorem patches_cover {n : ℕ} (v : Sphere (n + 1)) : v ∈ patch n ∨ v ∈ southPatch n := by
  by_cases h : v ∈ patch n
  · exact Or.inl h
  · right
    have hz : denominator v = 0 := not_ne_iff.mp h
    change denominator (antipode v) ≠ 0
    have he : denominator v + denominator (antipode v) = 2 := by
      simp [denominator, antipode]
      ring
    intro hz'
    rw [hz, hz'] at he
    norm_num at he

def southSection {n : ℕ} (v : southPatch (n + 1)) : Block.Group (n + 2) :=
  correctRight (-unitarySection ⟨antipode v.val, v.property⟩)

theorem projection_southSection {n : ℕ} (v : southPatch (n + 1)) :
    projection (southSection v) = v.val := by
  apply Subtype.ext
  ext i
  change (correctRight (-unitarySection ⟨antipode v.val, v.property⟩)).val
    i (Fin.last (n + 1)) = v.val.val i
  rw [correctRight_last_column]
  change -(unitarySection ⟨antipode v.val, v.property⟩).val i _ = _
  rw [unitarySection_last_column]
  exact neg_neg _

theorem southSection_continuous (n : ℕ) : Continuous (@southSection n) := by
  apply (correctRight_continuous n).comp
  have ha : Continuous (fun v : southPatch (n + 1) =>
      (⟨antipode v.val, v.property⟩ : patch (n + 1))) :=
    continuous_induced_rng.mpr ((antipode_continuous _).comp continuous_subtype_val)
  apply continuous_induced_rng.mpr
  exact (((unitarySection_continuous _).comp ha).subtype_val).neg

theorem projection_surjective (n : ℕ) : Function.Surjective (@projection (n + 1)) := by
  intro v
  rcases patches_cover v with hv | hv
  · exact ⟨specialSection ⟨v, hv⟩, projection_specialSection _⟩
  · exact ⟨southSection ⟨v, hv⟩, projection_southSection _⟩

end

end Math.SUN.SphereSection
