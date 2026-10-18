import Mathlib.LinearAlgebra.SymplecticGroup
import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# The compact unitary symplectic matrix group

USp(2n), also denoted Sp(n), is the closed subgroup of U(2n) preserving
mathlib's standard alternating form. This is not the real split symplectic
group or the full complex algebraic symplectic group.
-/

set_option autoImplicit false

namespace Math.CompactSymplectic

noncomputable section

abbrev Index (n : ℕ) := Fin n ⊕ Fin n
abbrev Mat (n : ℕ) := Matrix (Index n) (Index n) ℂ

theorem star_mem_symplectic {n : ℕ} {A : Mat n}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℂ) :
    star A ∈ Matrix.symplecticGroup (Fin n) ℂ := by
  exact SymplecticGroup.map_mem (SymplecticGroup.transpose_mem hA) (starRingEnd ℂ)

def subgroup (n : ℕ) : Subgroup (Matrix.unitaryGroup (Index n) ℂ) where
  carrier := {g | g.val ∈ Matrix.symplecticGroup (Fin n) ℂ}
  one_mem' := (Matrix.symplecticGroup (Fin n) ℂ).one_mem
  mul_mem' ha hb := (Matrix.symplecticGroup (Fin n) ℂ).mul_mem ha hb
  inv_mem' hg := star_mem_symplectic hg

abbrev Group (n : ℕ) := subgroup n

def matrix {n : ℕ} (g : Group n) : Mat n := g.val.val

@[simp] theorem matrix_one (n : ℕ) : matrix (1 : Group n) = 1 := rfl
@[simp] theorem matrix_mul {n : ℕ} (g h : Group n) : matrix (g * h) = matrix g * matrix h := rfl
@[simp] theorem matrix_inv {n : ℕ} (g : Group n) : matrix g⁻¹ = star (matrix g) := rfl

theorem matrix_injective (n : ℕ) : Function.Injective (matrix (n := n)) := by
  intro g h he
  apply Subtype.ext
  exact Subtype.ext he

theorem matrix_unitary {n : ℕ} (g : Group n) :
    matrix g ∈ Matrix.unitaryGroup (Index n) ℂ := g.val.property

theorem matrix_symplectic {n : ℕ} (g : Group n) :
    matrix g ∈ Matrix.symplecticGroup (Fin n) ℂ := g.property

theorem matrix_det {n : ℕ} (g : Group n) : (matrix g).det = 1 :=
  SymplecticGroup.det_eq_one (matrix_symplectic g)

theorem subgroup_isClosed (n : ℕ) :
    IsClosed (subgroup n : Set (Matrix.unitaryGroup (Index n) ℂ)) := by
  change IsClosed {g : Matrix.unitaryGroup (Index n) ℂ |
    g.val * Matrix.J (Fin n) ℂ * g.val.transpose = Matrix.J (Fin n) ℂ}
  exact isClosed_eq (by fun_prop) continuous_const

instance (n : ℕ) : CompactSpace (Group n) :=
  isCompact_iff_compactSpace.mp (subgroup_isClosed n).isCompact

theorem matrix_continuous (n : ℕ) : Continuous (matrix (n := n)) :=
  continuous_subtype_val.comp continuous_subtype_val

def toSymplectic (n : ℕ) : Group n →* Matrix.symplecticGroup (Fin n) ℂ where
  toFun g := ⟨matrix g, matrix_symplectic g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def toSpecialUnitary (n : ℕ) : Group n →* Matrix.specialUnitaryGroup (Index n) ℂ where
  toFun g := ⟨matrix g, matrix_unitary g, matrix_det g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toSpecialUnitary_injective (n : ℕ) : Function.Injective (toSpecialUnitary n) := by
  intro g h he
  exact matrix_injective n
    (congrArg (fun A : Matrix.specialUnitaryGroup (Index n) ℂ => A.val) he)

theorem toSpecialUnitary_continuous (n : ℕ) : Continuous (toSpecialUnitary n) :=
  continuous_induced_rng.mpr (matrix_continuous n)

end

end Math.CompactSymplectic
