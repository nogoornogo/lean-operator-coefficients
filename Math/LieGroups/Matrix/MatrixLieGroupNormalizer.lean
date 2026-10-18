import TauCeti.Topology.Algebra.UnitaryGroup
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Math.LieGroups.Matrix.LieNormalizerExponential
import Math.LieGroups.SpecialUnitary.SpecialUnitaryExponentialCriterion

/-!
# Closed special-unitary normalizer of a real matrix Lie algebra

This constructs a compact topological subgroup, not its connected component,
global form or a Lie-group structure on the subgroup.
-/

set_option autoImplicit false

namespace Math.MatrixLieGroupNormalizer

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open NormedSpace

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Special := Matrix.specialUnitaryGroup n ℂ

def conjugate (g : Special (n := n)) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  (g : Matrix n n ℂ) * X * (↑(g⁻¹) : Matrix n n ℂ)

@[simp] theorem conjugate_one (X : Matrix n n ℂ) : conjugate 1 X = X := by
  simp [conjugate]

theorem conjugate_mul (g h : Special (n := n)) (X : Matrix n n ℂ) :
    conjugate (g * h) X = conjugate g (conjugate h X) := by
  simp only [conjugate, mul_inv_rev, Submonoid.coe_mul, mul_assoc]

theorem continuous_conjugate (X : Matrix n n ℂ) :
    Continuous (fun g : Special (n := n) => conjugate g X) := by
  unfold conjugate
  exact (continuous_subtype_val.mul continuous_const).mul
    (continuous_subtype_val.comp continuous_inv)

variable (L : LieSubalgebra ℝ (Matrix n n ℂ))

/-- Conjugation preserves the real algebra in both directions. -/
def subgroup : Subgroup (Special (n := n)) where
  carrier := {g | (∀ X ∈ L, conjugate g X ∈ L) ∧ (∀ X ∈ L, conjugate g⁻¹ X ∈ L)}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    constructor
    · intro X hX
      rw [conjugate_mul]
      exact hg.1 _ (hh.1 _ hX)
    · intro X hX
      rw [mul_inv_rev, conjugate_mul]
      exact hh.2 _ (hg.2 _ hX)
  inv_mem' {g} hg := ⟨hg.2, by simpa using hg.1⟩

theorem mem_subgroup (g : Special (n := n)) : g ∈ subgroup L ↔
    (∀ X ∈ L, conjugate g X ∈ L) ∧ (∀ X ∈ L, conjugate g⁻¹ X ∈ L) := Iff.rfl

theorem isClosed_subgroup : IsClosed (subgroup L : Set (Special (n := n))) := by
  have hL : IsClosed (L : Set (Matrix n n ℂ)) := L.toSubmodule.closed_of_finiteDimensional
  change IsClosed {g | (∀ X ∈ L, conjugate g X ∈ L) ∧ (∀ X ∈ L, conjugate g⁻¹ X ∈ L)}
  apply IsClosed.inter
  · change IsClosed {g : Special | ∀ X ∈ L, conjugate g X ∈ L}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun X => isClosed_iInter fun _ => hL.preimage (continuous_conjugate X)
  · change IsClosed {g : Special | ∀ X ∈ L, conjugate g⁻¹ X ∈ L}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun X => isClosed_iInter fun _ =>
      hL.preimage ((continuous_conjugate X).comp continuous_inv)

instance : CompactSpace (subgroup L) := isCompact_iff_compactSpace.mp (isClosed_subgroup L).isCompact

/-- The same subgroup viewed as actual matrices, not an assumed named group. -/
def matrixCarrier : Submonoid (Matrix n n ℂ) :=
  (subgroup L).toSubmonoid.map (Matrix.specialUnitaryGroup n ℂ).subtype

theorem mem_matrixCarrier (A : Matrix n n ℂ) : A ∈ matrixCarrier L ↔
    ∃ g : Special (n := n), g ∈ subgroup L ∧ (g : Matrix n n ℂ) = A := Iff.rfl

theorem matrixCarrier_le_special : matrixCarrier L ≤ Matrix.specialUnitaryGroup n ℂ := by
  rintro A ⟨g, _, rfl⟩
  exact g.property

theorem inverse_coe_exp (X : Matrix n n ℂ) (hs : Xᴴ = -X) (t : ℝ)
    (g : Special (n := n)) (hg : (g : Matrix n n ℂ) = exp (t • X)) :
    (↑(g⁻¹) : Matrix n n ℂ) = exp (-(t • X)) := by
  change star (g : Matrix n n ℂ) = _
  rw [hg, star_exp, star_smul, star_trivial, Matrix.star_eq_conjTranspose, hs, smul_neg]

/-- An all-time matrix criterion; it makes no claim about manifold tangent spaces. -/
theorem exp_mem_matrixCarrier_iff (X : Matrix n n ℂ) :
    (∀ t : ℝ, exp (t • X) ∈ matrixCarrier L) ↔
      X ∈ L.normalizer ∧ Xᴴ = -X ∧ Matrix.trace X = 0 := by
  have hL : IsClosed (L : Set (Matrix n n ℂ)) := L.toSubmodule.closed_of_finiteDimensional
  constructor
  · intro h
    obtain ⟨hs, ht⟩ := (SpecialUnitaryExponentialCriterion.exp_mem_iff X).mp
      (fun t => matrixCarrier_le_special L (h t))
    refine ⟨(LieNormalizerExponential.normalizes_iff_exp_conjugate_mem L hL X).mpr ?_, hs, ht⟩
    intro t Y hY
    obtain ⟨g, hg, he⟩ := (mem_matrixCarrier L _).mp (h t)
    have hi := inverse_coe_exp X hs t g he
    have hc := hg.1 Y hY
    change (g : Matrix n n ℂ) * Y * (↑(g⁻¹) : Matrix n n ℂ) ∈ L at hc
    rw [he, hi] at hc
    exact hc
  · rintro ⟨hn, hs, ht⟩ t
    let g : Special (n := n) :=
      ⟨exp (t • X), (SpecialUnitaryExponentialCriterion.exp_mem_iff X).mpr ⟨hs, ht⟩ t⟩
    refine ⟨g, ?_, rfl⟩
    have hi := inverse_coe_exp X hs t g rfl
    constructor
    · intro Y hY
      change exp (t • X) * Y * (↑(g⁻¹) : Matrix n n ℂ) ∈ L
      rw [hi]
      exact LieNormalizerExponential.exp_conjugate_mem L hL X hn t Y hY
    · intro Y hY
      change (↑(g⁻¹) : Matrix n n ℂ) * Y * (↑((g⁻¹)⁻¹) : Matrix n n ℂ) ∈ L
      rw [inv_inv, hi]
      simpa only [neg_smul, neg_neg] using
        LieNormalizerExponential.exp_conjugate_mem L hL X hn (-t) Y hY

end

end Math.MatrixLieGroupNormalizer
