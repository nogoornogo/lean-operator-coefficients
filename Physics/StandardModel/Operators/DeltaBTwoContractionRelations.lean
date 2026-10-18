import Physics.StandardModel.Operators.DeltaBTwoSixQuark
import Math.RepresentationTheory.SixSlotSpeciesSum

open Math

/-!
# Exact color and Weyl identities for six-quark contractions

The color tensors use exactly the index order of Eqs. (2) and (3) of
arXiv:1901.07519.  This file proves their permutation types and the
two-component Schouten relation.  It does not identify an ordered polynomial
with a fermionic operator before exterior alternatization.
-/

namespace GUT.DeltaBTwoContractionRelations

set_option autoImplicit false
noncomputable section

open SMEpsilonTensor

abbrev Spin := WeylSpinor.Space

/-- `T^{SSS}_{\{ij\}\{kl\}\{mn\}}` in the paper's index order. -/
def colorSSS (i j k l m n : Color) : ℂ :=
  eps3 i k m * eps3 j l n + eps3 j k m * eps3 i l n +
    eps3 i l m * eps3 j k n + eps3 j l m * eps3 i k n

/-- `T^{AAS}_{[ij][kl]\{mn\}}` in the paper's index order. -/
def colorAAS (i j k l m n : Color) : ℂ :=
  eps3 i j m * eps3 k l n + eps3 i j n * eps3 k l m

theorem eps2_swap (a b : Spin) : eps2 b a = -eps2 a b := by
  simp [eps2]
  ring

/-- The two-component Schouten identity. -/
theorem weyl_schouten (a b c d : Spin) :
    eps2 a b * eps2 c d - eps2 a c * eps2 b d +
      eps2 a d * eps2 b c = 0 := by
  simp [eps2]
  ring

theorem colorSSS_swap_first (i j k l m n : Color) :
    colorSSS j i k l m n = colorSSS i j k l m n := by
  simp [colorSSS, eps3]
  ring

theorem colorSSS_swap_second (i j k l m n : Color) :
    colorSSS i j l k m n = colorSSS i j k l m n := by
  simp [colorSSS, eps3]
  ring

theorem colorSSS_swap_third (i j k l m n : Color) :
    colorSSS i j k l n m = colorSSS i j k l m n := by
  simp [colorSSS, eps3]
  ring

theorem colorAAS_swap_first (i j k l m n : Color) :
    colorAAS j i k l m n = -colorAAS i j k l m n := by
  simp [colorAAS, eps3]
  ring

theorem colorAAS_swap_second (i j k l m n : Color) :
    colorAAS i j l k m n = -colorAAS i j k l m n := by
  simp [colorAAS, eps3]
  ring

theorem colorAAS_swap_third (i j k l m n : Color) :
    colorAAS i j k l n m = colorAAS i j k l m n := by
  simp [colorAAS, eps3]
  ring

theorem colorSSS_invariant (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (i j k l m n : Color) :
    colorSSS (g.1.mulVec i) (g.1.mulVec j) (g.1.mulVec k)
      (g.1.mulVec l) (g.1.mulVec m) (g.1.mulVec n) =
        colorSSS i j k l m n := by
  simp only [colorSSS, eps3_invariant _ g.property]

theorem colorAAS_invariant (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (i j k l m n : Color) :
    colorAAS (g.1.mulVec i) (g.1.mulVec j) (g.1.mulVec k)
      (g.1.mulVec l) (g.1.mulVec m) (g.1.mulVec n) =
        colorAAS i j k l m n := by
  simp only [colorAAS, eps3_invariant _ g.property]

/-- Conventional `O¹_RRR` evaluated on the repository's interleaved ordered
slots `(u₁,d₁,u₂,d₂,d₃,d₄)`.  The minus sign is the fermionic
reordering from `(u₁,u₂,d₁,d₂,d₃,d₄)`. -/
def orderedO1Value
    (a b c d e f : Color) (s t u v w x : Spin) : ℂ :=
  -colorSSS a c b d e f * (eps2 s u * eps2 t v * eps2 w x)

/-- Conventional `O²_RRR` on interleaved ordered slots. -/
def orderedO2Value
    (a b c d e f : Color) (s t u v w x : Spin) : ℂ :=
  colorSSS a b c d e f * (eps2 s t * eps2 u v * eps2 w x)

/-- Conventional `O³_RRR` on interleaved ordered slots. -/
def orderedO3Value
    (a b c d e f : Color) (s t u v w x : Spin) : ℂ :=
  colorAAS a b c d e f * (eps2 s t * eps2 u v * eps2 w x)

theorem orderedO3Value_eq_existing
    (a b c d e f : Color) (s t u v w x : Spin) :
    orderedO3Value a b c d e f s t u v w x =
      (eps3 a b e * eps3 c d f + eps3 a b f * eps3 c d e) *
        (eps2 s t * eps2 u v * eps2 w x) := by
  rfl

/-- Lexicographic enumeration of the 24 permutations of four down slots. -/
private def downPerm : Fin 24 → Fin 4 → Fin 4 := ![
  ![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 2, 3, 1],
  ![0, 3, 1, 2], ![0, 3, 2, 1], ![1, 0, 2, 3], ![1, 0, 3, 2],
  ![1, 2, 0, 3], ![1, 2, 3, 0], ![1, 3, 0, 2], ![1, 3, 2, 0],
  ![2, 0, 1, 3], ![2, 0, 3, 1], ![2, 1, 0, 3], ![2, 1, 3, 0],
  ![2, 3, 0, 1], ![2, 3, 1, 0], ![3, 0, 1, 2], ![3, 0, 2, 1],
  ![3, 1, 0, 2], ![3, 1, 2, 0], ![3, 2, 0, 1], ![3, 2, 1, 0]]

private def downSign : Fin 24 → ℂ := ![
  1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1,
  1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1]

/-- Antisymmetrize an interleaved ordered value over the two up slots and the
four down slots.  This is the 48-term restriction of full six-slot
alternatization to a pure degree `(2,4)` input. -/
def blockAlternation
    (F : (Color × Spin) → (Color × Spin) → (Color × Spin) →
      (Color × Spin) → (Color × Spin) → (Color × Spin) → ℂ)
    (u : Fin 2 → Color × Spin) (d : Fin 4 → Color × Spin) : ℂ :=
  ∑ p : Fin 24, downSign p *
    (F (u 0) (d (downPerm p 0)) (u 1) (d (downPerm p 1))
        (d (downPerm p 2)) (d (downPerm p 3)) -
      F (u 1) (d (downPerm p 0)) (u 0) (d (downPerm p 1))
        (d (downPerm p 2)) (d (downPerm p 3)))

theorem blockAlternation_eq (F : (Color × Spin) → (Color × Spin) →
    (Color × Spin) → (Color × Spin) → (Color × Spin) → (Color × Spin) → ℂ)
    (u : Fin 2 → Color × Spin) (d : Fin 4 → Color × Spin) :
    blockAlternation F u d = SixSlotSpeciesSum.blockSum F u d := by
  unfold blockAlternation SixSlotSpeciesSum.blockSum
  apply Finset.sum_congr rfl
  intro r hr
  fin_cases r <;> simp [downSign, downPerm, SixSlotSpeciesSum.downIndex,
    SixSlotSpeciesSum.downParity]

def valueO1 (a b c d e f : Color × Spin) : ℂ :=
  orderedO1Value a.1 b.1 c.1 d.1 e.1 f.1 a.2 b.2 c.2 d.2 e.2 f.2

def valueO2 (a b c d e f : Color × Spin) : ℂ :=
  orderedO2Value a.1 b.1 c.1 d.1 e.1 f.1 a.2 b.2 c.2 d.2 e.2 f.2

def valueO3 (a b c d e f : Color × Spin) : ℂ :=
  orderedO3Value a.1 b.1 c.1 d.1 e.1 f.1 a.2 b.2 c.2 d.2 e.2 f.2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem fierz_blockAlternation
    (u : Fin 2 → Color × Spin) (d : Fin 4 → Color × Spin) :
    blockAlternation valueO2 u d - blockAlternation valueO1 u d =
      3 * blockAlternation valueO3 u d := by
  classical
  simp [blockAlternation, downSign, downPerm, Fin.sum_univ_succ,
    valueO1, valueO2, valueO3, orderedO1Value,
    orderedO2Value, orderedO3Value, colorSSS, colorAAS, eps2, eps3,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

end
end GUT.DeltaBTwoContractionRelations
