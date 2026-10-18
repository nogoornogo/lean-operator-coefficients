import GUT.SU6.Hypercharge.ActualBlockCentralizer
import Mathlib.Analysis.Complex.Circle

/-!
# The compact block-scalar centralizer

At the coefficient level, a unitary block-scalar operator on blocks of
dimensions `3`, `2`, and `1` is specified by three circle elements
`(c, w, s)`.  The special-unitary determinant condition is

`c ^ 3 * w ^ 2 * s = 1`.

This file identifies that kernel, as a topological group, with
`Circle x Circle`.  It is deliberately independent of a choice of
decomposition equivalence: the latter need not be unitary.
-/

namespace GUT
namespace CompactBlockCentralizer

noncomputable section

/-- Ordered color, weak, and singlet unitary block coefficients. -/
abbrev BlockCoefficients := Circle × (Circle × Circle)

/-- The determinant of a scalar operator on blocks of dimensions `3`, `2`,
and `1`. -/
def blockDeterminant : BlockCoefficients →* Circle where
  toFun p := p.1 ^ 3 * p.2.1 ^ 2 * p.2.2
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, mul_pow]
    ac_rfl

@[simp]
theorem blockDeterminant_apply (p : BlockCoefficients) :
    blockDeterminant p = p.1 ^ 3 * p.2.1 ^ 2 * p.2.2 :=
  rfl

/-- The compact coefficient group satisfying the `SU(6)` determinant
condition. -/
abbrev Group := blockDeterminant.ker

/-- Build a determinant-one coefficient triple from independent color and
weak phases. -/
def ofColorWeak (p : Circle × Circle) : Group :=
  ⟨(p.1, (p.2, (p.1 ^ 3 * p.2 ^ 2)⁻¹)), by
    simp [blockDeterminant]⟩

@[simp]
theorem ofColorWeak_color (p : Circle × Circle) :
    (ofColorWeak p : BlockCoefficients).1 = p.1 :=
  rfl

@[simp]
theorem ofColorWeak_weak (p : Circle × Circle) :
    (ofColorWeak p : BlockCoefficients).2.1 = p.2 :=
  rfl

@[simp]
theorem ofColorWeak_singlet (p : Circle × Circle) :
    (ofColorWeak p : BlockCoefficients).2.2 =
      (p.1 ^ 3 * p.2 ^ 2)⁻¹ :=
  rfl

/-- Forget the singlet phase, which is forced by the determinant equation. -/
def toColorWeak (p : Group) : Circle × Circle :=
  ((p : BlockCoefficients).1, (p : BlockCoefficients).2.1)

@[simp]
theorem toColorWeak_ofColorWeak (p : Circle × Circle) :
    toColorWeak (ofColorWeak p) = p :=
  rfl

@[simp]
theorem ofColorWeak_toColorWeak (p : Group) :
    ofColorWeak (toColorWeak p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · have hp := p.property
      change
        (p.1.1 ^ 3 * p.1.2.1 ^ 2)⁻¹ = p.1.2.2
      change p.1.1 ^ 3 * p.1.2.1 ^ 2 * p.1.2.2 = 1 at hp
      exact (inv_eq_iff_mul_eq_one).2 hp

/-- The determinant-one block coefficients form an abstract two-torus. -/
def torusMulEquiv : (Circle × Circle) ≃* Group where
  toFun := ofColorWeak
  invFun := toColorWeak
  left_inv := toColorWeak_ofColorWeak
  right_inv := ofColorWeak_toColorWeak
  map_mul' p q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · simp only [ofColorWeak, Prod.fst_mul, Prod.snd_mul,
          Subgroup.coe_mul, mul_pow]
        simp only [mul_inv_rev]
        ac_rfl

@[simp]
theorem torusMulEquiv_apply (p : Circle × Circle) :
    torusMulEquiv p = ofColorWeak p :=
  rfl

@[simp]
theorem torusMulEquiv_symm_apply (p : Group) :
    torusMulEquiv.symm p = toColorWeak p :=
  rfl

/-- The abstract two-torus identification also preserves the topology. -/
def torusContinuousMulEquiv : (Circle × Circle) ≃ₜ* Group where
  __ := torusMulEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    change Continuous
      (fun p : Group =>
        ((p : BlockCoefficients).1, (p : BlockCoefficients).2.1))
    fun_prop

@[simp]
theorem torusContinuousMulEquiv_apply (p : Circle × Circle) :
    torusContinuousMulEquiv p = ofColorWeak p :=
  rfl

@[simp]
theorem torusContinuousMulEquiv_symm_apply (p : Group) :
    torusContinuousMulEquiv.symm p = toColorWeak p :=
  rfl

instance groupCompactSpace : CompactSpace Group :=
  torusContinuousMulEquiv.toHomeomorph.compactSpace

theorem compact_univ : IsCompact (Set.univ : Set Group) :=
  isCompact_univ

end

end CompactBlockCentralizer
end GUT
