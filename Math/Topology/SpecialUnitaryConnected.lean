import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import TauCeti.Topology.Algebra.UnitaryGroup

/-! A determinant-correcting retraction U(n) -> SU(n), and local path
connectedness in the actual matrix topology. This is not simple-connectedness. -/

set_option autoImplicit false
open scoped Matrix.Norms.L2Operator

namespace Math.SpecialUnitaryTopology

noncomputable section

abbrev Unitary (n : ℕ) := Matrix.unitaryGroup (Fin n) ℂ
abbrev Special (n : ℕ) := Matrix.specialUnitaryGroup (Fin n) ℂ

def forget (n : ℕ) : Special n → Unitary n := fun g => ⟨g.val, g.property.1⟩

def correction {n : ℕ} (g : Unitary (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then star g.val.det else 1)

theorem correction_unitary {n : ℕ} (g : Unitary (n + 1)) :
    correction g ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [correction, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = 0
  · simpa [hi] using (Matrix.det_of_mem_unitary g.property).1
  · simp [hi]

theorem correction_det {n : ℕ} (g : Unitary (n + 1)) :
    (correction g).det = star g.val.det := by
  simp [correction, Matrix.det_diagonal]

def retract (n : ℕ) (g : Unitary (n + 1)) : Special (n + 1) :=
  ⟨correction g * g.val,
    (Matrix.unitaryGroup _ ℂ).mul_mem (correction_unitary g) g.property, by
      change Matrix.det (correction g * g.val) = 1
      rw [Matrix.det_mul, correction_det]
      exact (Matrix.det_of_mem_unitary g.property).1⟩

theorem retract_forget (n : ℕ) (g : Special (n + 1)) : retract n (forget _ g) = g := by
  apply Subtype.ext
  have hd : g.val.det = 1 := g.property.2
  change correction (forget _ g) * g.val = g.val
  simp [correction, forget, hd]

theorem retract_surjective (n : ℕ) : Function.Surjective (retract n) :=
  fun g => ⟨forget _ g, retract_forget n g⟩

theorem retract_continuous (n : ℕ) : Continuous (retract n) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun g : Unitary (n + 1) => correction g * g.val)
  apply Continuous.mul _ continuous_subtype_val
  apply Continuous.matrix_diagonal
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · simp only [hi, ite_true]
    fun_prop
  · simp only [hi, ite_false]
    exact continuous_const

theorem retract_quotient (n : ℕ) : Topology.IsQuotientMap (retract n) :=
  Topology.IsQuotientMap.of_surjective_continuous (retract_surjective n) (retract_continuous n)

theorem locallyPathConnected (n : ℕ) : LocallyPathConnectedSpace (Special n) := by
  cases n with
  | zero => infer_instance
  | succ n => exact (retract_quotient n).locallyPathConnectedSpace

end

end Math.SpecialUnitaryTopology
