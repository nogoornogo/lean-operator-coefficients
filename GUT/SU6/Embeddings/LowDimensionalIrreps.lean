import GUT.SU6.Embeddings.SemisimpleEmbedding
import Mathlib.Tactic

/-!
# Low-dimensional highest-weight arithmetic for Claim semisimple embedding classification

This module proves the finite arithmetic consequences of the standard Weyl
dimension formulas needed by the semisimple embedding classification.  It does
not assert that every continuous irreducible representation of `SU(3)` or
`SU(2)` is classified by a highest weight; that representation-theoretic
classification remains an explicit bridge.
-/

namespace GUT
namespace LowDimensionalIrreps

/-!
## `SU(3)`

For highest weight `(a,b)`, the Weyl dimension formula is

`2 * dim = (a+1) * (b+1) * (a+b+2)`.
-/

def SU3TwiceDimension (a b : ℕ) : ℕ :=
  (a + 1) * (b + 1) * (a + b + 2)

/-- The only `SU(3)` highest weights of dimension at most six are the
trivial, fundamental, antifundamental, symmetric-square, and its conjugate
weights. -/
theorem su3_highestWeight_of_dimension_le_six
    (a b d : ℕ)
    (hFormula : 2 * d = SU3TwiceDimension a b)
    (hDim : d ≤ 6) :
    (a = 0 ∧ b = 0 ∧ d = 1) ∨
    (a = 1 ∧ b = 0 ∧ d = 3) ∨
    (a = 0 ∧ b = 1 ∧ d = 3) ∨
    (a = 2 ∧ b = 0 ∧ d = 6) ∨
    (a = 0 ∧ b = 2 ∧ d = 6) := by
  have hProduct : SU3TwiceDimension a b ≤ 12 := by
    omega
  have ha : a ≤ 2 := by
    by_contra h
    have ha3 : 3 ≤ a := by omega
    have h1 : 4 ≤ a + 1 := by omega
    have h2 : 1 ≤ b + 1 := by omega
    have h3 : 5 ≤ a + b + 2 := by omega
    have : 20 ≤ SU3TwiceDimension a b := by
      exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega
  have hb : b ≤ 2 := by
    by_contra h
    have hb3 : 3 ≤ b := by omega
    have h1 : 1 ≤ a + 1 := by omega
    have h2 : 4 ≤ b + 1 := by omega
    have h3 : 5 ≤ a + b + 2 := by omega
    have : 20 ≤ SU3TwiceDimension a b := by
      exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega
  interval_cases a <;> interval_cases b <;>
    norm_num [SU3TwiceDimension] at hFormula ⊢ <;> omega

theorem su3_dimension_mem_of_dimension_le_six
    (a b d : ℕ)
    (hFormula : 2 * d = SU3TwiceDimension a b)
    (hDim : d ≤ 6) :
    d ∈ ({1, 3, 6} : Finset ℕ) := by
  rcases su3_highestWeight_of_dimension_le_six a b d hFormula hDim with
    h | h | h | h | h <;> simp_all

/-!
## `SU(2)`

The irreducible highest weight `m` has dimension `m+1`.
-/

theorem su2_highestWeight_of_dimension_le_six
    (m d : ℕ) (hFormula : d = m + 1) (hDim : d ≤ 6) :
    (m = 0 ∧ d = 1) ∨ (m = 1 ∧ d = 2) ∨
    (m = 2 ∧ d = 3) ∨ (m = 3 ∧ d = 4) ∨
    (m = 4 ∧ d = 5) ∨ (m = 5 ∧ d = 6) := by
  omega

theorem su2_dimension_pos
    (m d : ℕ) (hFormula : d = m + 1) : 0 < d := by
  omega

/-- The weak center acts with sign `(-1)^m` on highest weight `m`; after
substituting `d=m+1`, this is the familiar `(-1)^(d-1)`. -/
theorem su2_center_exponent_eq_dimension_sub_one
    (m d : ℕ) (hFormula : d = m + 1) : m = d - 1 := by
  omega

/-!
## Product-block dimensions
-/

/-- Once the low-dimensional `SU(3)` dimension list is known, these are all
factorizations `d3*d2 ≤ 6` with a positive `SU(2)` dimension. -/
theorem product_block_dimensions_le_six
    (d3 d2 : ℕ)
    (h3 : d3 = 1 ∨ d3 = 3 ∨ d3 = 6)
    (h2 : 0 < d2)
    (hDim : d3 * d2 ≤ 6) :
    (d3 = 1 ∧ d2 = 1) ∨
    (d3 = 1 ∧ d2 = 2) ∨
    (d3 = 1 ∧ d2 = 3) ∨
    (d3 = 1 ∧ d2 = 4) ∨
    (d3 = 1 ∧ d2 = 5) ∨
    (d3 = 1 ∧ d2 = 6) ∨
    (d3 = 3 ∧ d2 = 1) ∨
    (d3 = 3 ∧ d2 = 2) ∨
    (d3 = 6 ∧ d2 = 1) := by
  rcases h3 with rfl | rfl | rfl <;> omega

/-!
## A sound finite block certificate

These constructors correspond exactly to the dimension pairs in
`product_block_dimensions_le_six`.  A list becomes a six-dimensional
decomposition only after its dimension and nontrivial-factor hypotheses have
been supplied.
-/

inductive BlockKind where
  | singlet
  | weak2
  | weak3
  | weak4
  | weak5
  | weak6
  | color3
  | color6
  | tensor32
  deriving DecidableEq, Repr

namespace BlockKind

def dimension : BlockKind → ℕ
  | singlet => 1
  | weak2 => 2
  | weak3 => 3
  | weak4 => 4
  | weak5 => 5
  | weak6 => 6
  | color3 => 3
  | color6 => 6
  | tensor32 => 6

def ColorActive : BlockKind → Prop
  | color3 | color6 | tensor32 => True
  | _ => False

def WeakActive : BlockKind → Prop
  | weak2 | weak3 | weak4 | weak5 | weak6 | tensor32 => True
  | _ => False

end BlockKind

/-- Every allowed factor-dimension pair has a unique semantic block kind:
`ColorActive` and `WeakActive` record exactly which factors are nontrivial. -/
theorem exists_blockKind_of_factor_dimensions_le_six
    (d3 d2 d : ℕ)
    (h3 : d3 ∈ ({1, 3, 6} : Finset ℕ))
    (h2 : 0 < d2)
    (hProduct : d3 * d2 = d)
    (hDim : d ≤ 6) :
    ∃ b : BlockKind, b.dimension = d ∧
      (b.ColorActive ↔ d3 ≠ 1) ∧
      (b.WeakActive ↔ d2 ≠ 1) := by
  subst d
  have h3' : d3 = 1 ∨ d3 = 3 ∨ d3 = 6 := by
    simpa using h3
  rcases product_block_dimensions_le_six d3 d2 h3' h2 hDim with
    h | h | h | h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.singlet, by simp [BlockKind.dimension, BlockKind.ColorActive,
      BlockKind.WeakActive]⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.weak2, by simp [BlockKind.dimension, BlockKind.ColorActive,
      BlockKind.WeakActive]⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.weak3, by simp [BlockKind.dimension, BlockKind.ColorActive,
      BlockKind.WeakActive]⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.weak4, by simp [BlockKind.dimension, BlockKind.ColorActive,
      BlockKind.WeakActive]⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.weak5, by simp [BlockKind.dimension, BlockKind.ColorActive,
      BlockKind.WeakActive]⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.weak6, by simp [BlockKind.dimension, BlockKind.ColorActive,
      BlockKind.WeakActive]⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.color3, by simp [BlockKind.dimension, BlockKind.ColorActive,
      BlockKind.WeakActive]⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.tensor32, by simp [BlockKind.dimension, BlockKind.ColorActive,
      BlockKind.WeakActive]⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.color6, by simp [BlockKind.dimension, BlockKind.ColorActive,
      BlockKind.WeakActive]⟩

structure RawBranchCounts where
  tensor32 : ℕ
  color3 : ℕ
  color6 : ℕ
  weak2 : ℕ
  weak3 : ℕ
  weak4 : ℕ
  weak5 : ℕ
  weak6 : ℕ
  singlet : ℕ
  deriving DecidableEq, Repr

namespace RawBranchCounts

def zero : RawBranchCounts :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def addBlock : BlockKind → RawBranchCounts → RawBranchCounts
  | .singlet, c => { c with singlet := c.singlet + 1 }
  | .weak2, c => { c with weak2 := c.weak2 + 1 }
  | .weak3, c => { c with weak3 := c.weak3 + 1 }
  | .weak4, c => { c with weak4 := c.weak4 + 1 }
  | .weak5, c => { c with weak5 := c.weak5 + 1 }
  | .weak6, c => { c with weak6 := c.weak6 + 1 }
  | .color3, c => { c with color3 := c.color3 + 1 }
  | .color6, c => { c with color6 := c.color6 + 1 }
  | .tensor32, c => { c with tensor32 := c.tensor32 + 1 }

/-- Read the multiplicity of one semantic block kind. -/
def multiplicity : BlockKind → RawBranchCounts → ℕ
  | .singlet, c => c.singlet
  | .weak2, c => c.weak2
  | .weak3, c => c.weak3
  | .weak4, c => c.weak4
  | .weak5, c => c.weak5
  | .weak6, c => c.weak6
  | .color3, c => c.color3
  | .color6, c => c.color6
  | .tensor32, c => c.tensor32

theorem multiplicity_addBlock (b x : BlockKind) (c : RawBranchCounts) :
    multiplicity b (addBlock x c) =
      (if x = b then 1 else 0) + multiplicity b c := by
  cases b <;> cases x <;>
    simp [multiplicity, addBlock] <;> omega

def ofList : List BlockKind → RawBranchCounts
  | [] => zero
  | b :: bs => addBlock b (ofList bs)

theorem multiplicity_ofList (b : BlockKind) (blocks : List BlockKind) :
    multiplicity b (ofList blocks) = blocks.count b := by
  induction blocks with
  | nil => cases b <;> rfl
  | cons x xs ih =>
      rw [ofList, multiplicity_addBlock, ih]
      by_cases h : x = b
      · subst x
        simp [Nat.add_comm]
      · simp [h]

def weightedDimension (c : RawBranchCounts) : ℕ :=
  6 * c.tensor32 + 3 * c.color3 + 6 * c.color6 +
    2 * c.weak2 + 3 * c.weak3 + 4 * c.weak4 +
    5 * c.weak5 + 6 * c.weak6 + c.singlet

def colorMultiplicity (c : RawBranchCounts) : ℕ :=
  c.tensor32 + c.color3 + c.color6

def weakMultiplicity (c : RawBranchCounts) : ℕ :=
  c.tensor32 + c.weak2 + c.weak3 + c.weak4 + c.weak5 + c.weak6

theorem weightedDimension_addBlock (b : BlockKind) (c : RawBranchCounts) :
    weightedDimension (addBlock b c) = BlockKind.dimension b + weightedDimension c := by
  cases b <;> simp [addBlock, weightedDimension, BlockKind.dimension] <;> omega

theorem weightedDimension_ofList (blocks : List BlockKind) :
    weightedDimension (ofList blocks) =
      (blocks.map BlockKind.dimension).sum := by
  induction blocks with
  | nil => simp [ofList, zero, weightedDimension]
  | cons b bs ih =>
      simp [ofList, weightedDimension_addBlock, ih]

theorem colorMultiplicity_le_addBlock (b : BlockKind) (c : RawBranchCounts) :
    colorMultiplicity c ≤ colorMultiplicity (addBlock b c) := by
  cases b <;> simp [colorMultiplicity, addBlock]

theorem colorMultiplicity_addBlock_pos_of_active
    (b : BlockKind) (c : RawBranchCounts) (h : b.ColorActive) :
    0 < colorMultiplicity (addBlock b c) := by
  cases b <;>
    simp_all [colorMultiplicity, addBlock, BlockKind.ColorActive]

theorem colorMultiplicity_ofList_pos (blocks : List BlockKind)
    (h : ∃ b ∈ blocks, b.ColorActive) :
    0 < colorMultiplicity (ofList blocks) := by
  induction blocks with
  | nil => simp at h
  | cons b bs ih =>
      rcases h with ⟨x, hx, hActive⟩
      simp only [List.mem_cons] at hx
      rcases hx with hxb | hx
      · subst x
        exact colorMultiplicity_addBlock_pos_of_active b (ofList bs) hActive
      · have hTail := ih ⟨x, hx, hActive⟩
        change 0 < colorMultiplicity (addBlock b (ofList bs))
        exact lt_of_lt_of_le hTail
          (colorMultiplicity_le_addBlock b (ofList bs))

theorem weakMultiplicity_le_addBlock (b : BlockKind) (c : RawBranchCounts) :
    weakMultiplicity c ≤ weakMultiplicity (addBlock b c) := by
  cases b <;> simp [weakMultiplicity, addBlock]

theorem weakMultiplicity_addBlock_pos_of_active
    (b : BlockKind) (c : RawBranchCounts) (h : b.WeakActive) :
    0 < weakMultiplicity (addBlock b c) := by
  cases b <;>
    simp_all [weakMultiplicity, addBlock, BlockKind.WeakActive]

theorem weakMultiplicity_ofList_pos (blocks : List BlockKind)
    (h : ∃ b ∈ blocks, b.WeakActive) :
    0 < weakMultiplicity (ofList blocks) := by
  induction blocks with
  | nil => simp at h
  | cons b bs ih =>
      rcases h with ⟨x, hx, hActive⟩
      simp only [List.mem_cons] at hx
      rcases hx with hxb | hx
      · subst x
        exact weakMultiplicity_addBlock_pos_of_active b (ofList bs) hActive
      · have hTail := ih ⟨x, hx, hActive⟩
        change 0 < weakMultiplicity (addBlock b (ofList bs))
        exact lt_of_lt_of_le hTail
          (weakMultiplicity_le_addBlock b (ofList bs))

end RawBranchCounts

structure SixDimensionalBlockDecomposition where
  blocks : List BlockKind
  dimension : (blocks.map BlockKind.dimension).sum = 6
  color_nontrivial : ∃ b ∈ blocks, b.ColorActive
  weak_nontrivial : ∃ b ∈ blocks, b.WeakActive

namespace SixDimensionalBlockDecomposition

def toBranchCounts (D : SixDimensionalBlockDecomposition) :
    SemisimpleEmbedding.SixDimensionalBranchCounts := by
  let c := RawBranchCounts.ofList D.blocks
  refine
    { tensor32 := c.tensor32
      color3 := c.color3
      color6 := c.color6
      weak2 := c.weak2
      weak3 := c.weak3
      weak4 := c.weak4
      weak5 := c.weak5
      weak6 := c.weak6
      singlet := c.singlet
      dimension := ?_
      color_nontrivial := ?_
      weak_nontrivial := ?_ }
  · change RawBranchCounts.weightedDimension c = 6
    rw [RawBranchCounts.weightedDimension_ofList]
    exact D.dimension
  · change 0 < RawBranchCounts.colorMultiplicity c
    exact RawBranchCounts.colorMultiplicity_ofList_pos D.blocks
      D.color_nontrivial
  · change 0 < RawBranchCounts.weakMultiplicity c
    exact RawBranchCounts.weakMultiplicity_ofList_pos D.blocks
      D.weak_nontrivial

/-- Every certified six-dimensional low-irrep block list has one of the three
branch shapes proved in `SemisimpleEmbedding`. -/
theorem classify (D : SixDimensionalBlockDecomposition) :
    D.toBranchCounts.IsTensorProductBranch ∨
      D.toBranchCounts.IsWeakDoubletBlock ∨
      D.toBranchCounts.IsWeakTripletBlock :=
  D.toBranchCounts.classify

/-- The weak-doublet branch count equations determine the whole block list,
up to the irrelevant ordering of irreducible summands. -/
theorem blocks_perm_color3_weak2_singlet_of_isWeakDoubletBlock
    (D : SixDimensionalBlockDecomposition)
    (hDoublet : D.toBranchCounts.IsWeakDoubletBlock) :
    List.Perm D.blocks [.color3, .weak2, .singlet] := by
  apply List.perm_iff_count.mpr
  intro b
  rw [← RawBranchCounts.multiplicity_ofList]
  simp [SemisimpleEmbedding.SixDimensionalBranchCounts.IsWeakDoubletBlock,
    toBranchCounts] at hDoublet
  rcases hDoublet with ⟨hTensor, hColor3, hColor6, hWeak2, hWeak3,
    hWeak4, hWeak5, hWeak6, hSinglet⟩
  cases b <;> simp [RawBranchCounts.multiplicity] <;> assumption

/-- In the weak-doublet branch, every actual constituent is one of the three
standard semantic blocks. -/
theorem block_eq_color3_or_weak2_or_singlet_of_isWeakDoubletBlock
    (D : SixDimensionalBlockDecomposition)
    (hDoublet : D.toBranchCounts.IsWeakDoubletBlock)
    {b : BlockKind} (hb : b ∈ D.blocks) :
    b = .color3 ∨ b = .weak2 ∨ b = .singlet := by
  have hPerm :=
    D.blocks_perm_color3_weak2_singlet_of_isWeakDoubletBlock hDoublet
  have : b ∈ [.color3, .weak2, .singlet] := hPerm.subset hb
  simpa using this

/-- In the weak-triplet branch, every actual constituent in the certified
block list is either the color triplet or the weak triplet. -/
theorem block_eq_color3_or_weak3_of_isWeakTripletBlock
    (D : SixDimensionalBlockDecomposition)
    (hTriplet : D.toBranchCounts.IsWeakTripletBlock)
    {b : BlockKind} (hb : b ∈ D.blocks) :
    b = .color3 ∨ b = .weak3 := by
  have hCount : 0 < D.blocks.count b := List.count_pos_iff.mpr hb
  rw [← RawBranchCounts.multiplicity_ofList] at hCount
  cases b with
  | color3 => exact Or.inl rfl
  | weak3 => exact Or.inr rfl
  | singlet | weak2 | weak4 | weak5 | weak6 | color6 | tensor32 =>
      simp only [SemisimpleEmbedding.SixDimensionalBranchCounts.IsWeakTripletBlock]
        at hTriplet
      simp [toBranchCounts, RawBranchCounts.multiplicity] at hCount hTriplet
      omega

end SixDimensionalBlockDecomposition

end LowDimensionalIrreps
end GUT
