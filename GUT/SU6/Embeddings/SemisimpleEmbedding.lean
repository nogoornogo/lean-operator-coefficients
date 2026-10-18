import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Tactic

/-!
# The finite core of the semisimple embedding classification

This module isolates two parts of Claim semisimple embedding classification that do not require a classification
library for compact Lie-group representations.

First, after complete reducibility and the low-dimensional irreducible
representations of `SU(3)` and `SU(2)` have been supplied, dimension six leaves
exactly three numerical decomposition shapes:

* `(3,2)`;
* `(3,1) + (1,2) + (1,1)`;
* `(3,1) + (1,3)`.

The last shape is a Lie-algebra embedding but its `SU(2)` action kills the
nontrivial central element.  The general kernel lemma below proves that no
representation pulled back along such a homomorphism can contain a weak
doublet which detects that element.

The first shape is a genuine counterexample to the unqualified statement that
the existence of weak doublets alone forces the block embedding.  It must be
excluded by the additional Standard Model requirement of a commuting
hypercharge `U(1)`; its defining product representation has only scalar
commutant.  Proving that commutant statement, and constructing the numerical
certificate below from every continuous embedding, are kept as explicit
representation-theoretic bridge tasks.
-/

namespace GUT
namespace SemisimpleEmbedding

/-!
## Six-dimensional dimension count

The fields count irreducible summands by their dimensions.  `tensor32` includes
both `(3,2)` and `(3-bar,2)`, while `color3` includes `(3,1)` and
`(3-bar,1)`.  The `color6` field records the possible six-dimensional color
irreducibles.  The weak fields record `(1,n)` for `2 <= n <= 6`.

Thus the structure deliberately starts after the standard low-dimensional
irreducible-classification theorem.  Its theorem below is the finite arithmetic
core of the embedding classification, not that missing Lie-theoretic theorem.
-/

structure SixDimensionalBranchCounts where
  tensor32 : ℕ
  color3 : ℕ
  color6 : ℕ
  weak2 : ℕ
  weak3 : ℕ
  weak4 : ℕ
  weak5 : ℕ
  weak6 : ℕ
  singlet : ℕ
  dimension :
    6 * tensor32 + 3 * color3 + 6 * color6 +
      2 * weak2 + 3 * weak3 + 4 * weak4 +
      5 * weak5 + 6 * weak6 + singlet = 6
  color_nontrivial : 0 < tensor32 + color3 + color6
  weak_nontrivial :
    0 < tensor32 + weak2 + weak3 + weak4 + weak5 + weak6

namespace SixDimensionalBranchCounts

def IsTensorProductBranch (c : SixDimensionalBranchCounts) : Prop :=
  c.tensor32 = 1 ∧ c.color3 = 0 ∧ c.color6 = 0 ∧
    c.weak2 = 0 ∧ c.weak3 = 0 ∧ c.weak4 = 0 ∧
    c.weak5 = 0 ∧ c.weak6 = 0 ∧ c.singlet = 0

def IsWeakDoubletBlock (c : SixDimensionalBranchCounts) : Prop :=
  c.tensor32 = 0 ∧ c.color3 = 1 ∧ c.color6 = 0 ∧
    c.weak2 = 1 ∧ c.weak3 = 0 ∧ c.weak4 = 0 ∧
    c.weak5 = 0 ∧ c.weak6 = 0 ∧ c.singlet = 1

def IsWeakTripletBlock (c : SixDimensionalBranchCounts) : Prop :=
  c.tensor32 = 0 ∧ c.color3 = 1 ∧ c.color6 = 0 ∧
    c.weak2 = 0 ∧ c.weak3 = 1 ∧ c.weak4 = 0 ∧
    c.weak5 = 0 ∧ c.weak6 = 0 ∧ c.singlet = 0

/--
The finite arithmetic core: a six-dimensional product representation on which
both simple factors act nontrivially has one of exactly three decomposition
shapes, once the standard low-dimensional irreducible list has been supplied.
-/
theorem classify (c : SixDimensionalBranchCounts) :
    c.IsTensorProductBranch ∨ c.IsWeakDoubletBlock ∨ c.IsWeakTripletBlock := by
  rcases c with
    ⟨tensor32, color3, color6, weak2, weak3, weak4, weak5, weak6, singlet,
      dimension, color_nontrivial, weak_nontrivial⟩
  simp only [IsTensorProductBranch, IsWeakDoubletBlock, IsWeakTripletBlock]
  omega

/--
Once the tensor-product branch is excluded by a commuting hypercharge and the
triplet branch is excluded by the weak-center test, the standard block shape is
forced.
-/
theorem isWeakDoubletBlock_of_not_tensorProduct_of_not_weakTriplet
    (c : SixDimensionalBranchCounts)
    (hTensor : ¬ c.IsTensorProductBranch)
    (hTriplet : ¬ c.IsWeakTripletBlock) :
    c.IsWeakDoubletBlock := by
  rcases c.classify with h | h | h
  · exact (hTensor h).elim
  · exact h
  · exact (hTriplet h).elim

end SixDimensionalBranchCounts

/-!
## The weak-center kernel obstruction
-/

section KernelObstruction

variable {k G H V W : Type*}
variable [Semiring k] [Monoid G] [Monoid H]
variable [AddCommMonoid V] [Module k V]
variable [AddCommMonoid W] [Module k W]

/-- Every element in the kernel of an embedding acts trivially after pullback. -/
theorem restrictedRepresentation_apply_of_mem_ker
    (φ : G →* H) (ρ : Representation k H V) (z : G)
    (hz : φ z = 1) :
    (ρ.comp φ) z = LinearMap.id := by
  ext v
  simp [hz]

/--
If `σ` occurs through an injective intertwiner in a representation restricted
along `φ`, every element of `ker φ` acts trivially on `σ` as well.
-/
theorem kernel_element_acts_trivially_on_subrepresentation
    (φ : G →* H) (ρ : Representation k H V)
    (σ : Representation k G W)
    (f : Representation.IntertwiningMap σ (ρ.comp φ))
    (hf : Function.Injective f) (z : G) (hz : φ z = 1) (w : W) :
    σ z w = w := by
  apply hf
  rw [f.isIntertwining]
  simp [hz]

/--
A representation which detects a kernel element cannot occur as a
subrepresentation of any pullback along that homomorphism.

For the alternative `(3,1) + (1,3)` branch, take `z` to be the nontrivial
center of `SU(2)`: the triplet kills `z`, whereas the defining weak doublet
moves every nonzero vector.
-/
theorem no_kernel_detecting_subrepresentation
    (φ : G →* H) (ρ : Representation k H V)
    (σ : Representation k G W) (z : G) (hz : φ z = 1)
    (hDetects : ∃ w, σ z w ≠ w) :
    ¬ ∃ f : Representation.IntertwiningMap σ (ρ.comp φ),
        Function.Injective f := by
  rintro ⟨f, hf⟩
  rcases hDetects with ⟨w, hw⟩
  exact hw (kernel_element_acts_trivially_on_subrepresentation
    φ ρ σ f hf z hz w)

end KernelObstruction

end SemisimpleEmbedding
end GUT
