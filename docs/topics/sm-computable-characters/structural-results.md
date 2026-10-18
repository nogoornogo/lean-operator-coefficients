# Structural support: proved adapters and current boundary

This continuation implements the [structural plan](structural-plan.md).
The Cauchy maps, complementary exterior duality, sharp weight bound and
lower-half Q/L constituent constructions below are proved without new
literature premises. The subsequent [signed/mixed result](signed-mixed-results.md)
closes the original-Higgs/q/l iff and individual admissible tests for all
four constant Q/L families. The full arbitrary-m (including inadmissible
constituents) and arbitrary mixed support programs remain separate.
Numerical multiplicity/rank equalities are not this continuation's endpoint.

## Proved mathematical interfaces

- [SymmetricPurePowers](../../../Math/LinearAlgebra/SymmetricPurePowers.lean)
  derives spanning by pure powers from pinned TauCeti's polarization identity.
  Linear maps on symmetric powers, and maps on their tensor products, can be
  compared on pure powers. No coordinate enumeration or numerical dimension
  is supplied.
- [TopExteriorCauchy](../../../Math/RepresentationTheory/TopExteriorCauchy.lean)
  constructs `Symⁿ B → Λⁿ(A ⊗ B)` from an n-vector frame by finite
  symmetrization. On a pure power it is the wedge of `a_i ⊗ v`.
  Naturality and the basis-change determinant factor are proved. For a basis
  of A, a determinant-one action on A gives an intertwiner. One normalized
  dual evaluation proves nonvanishing; irreducibility of the source then
  proves injectivity.
- [SymmetricCauchy](../../../Math/RepresentationTheory/SymmetricCauchy.lean)
  constructs the row map `Symⁿ B ⊗ Symⁿ C → Symⁿ(B ⊗ C)` by separate
  symmetrization. It is natural and has the expected pure-power formula.
  [ExtremeCauchyBlocks](../../../Math/RepresentationTheory/ExtremeCauchyBlocks.lean)
  composes row and column maps with their actual group actions.
- [SU2ExteriorBlocks](../../../Math/RepresentationTheory/SU2ExteriorBlocks.lean)
  proves column injectivity for the SU(2) doublet and row-column injectivity
  for two independently acting doublets. This uses the existing symmetric-power
  and external-product irreducibility theorems; no branching assertion is an
  extra premise.
- [GenerationExteriorBlocks](../../../Math/RepresentationTheory/GenerationExteriorBlocks.lean)
  embeds exterior products in two or three independent generation summands
  into `Λⁿ(V ⊗ ℂ³)`, preserving the action and injectivity. The proof uses
  the graded binary exterior product and an explicitly split generation map.
  It does not assert injectivity of arbitrary multiplication in an exterior
  algebra.
- [SU2SymmetricSupport](../../../Math/RepresentationTheory/SU2SymmetricSupport.lean)
  constructs injective constituent maps for every even m ≤ 2k in
  `Symᵏ ⊗ Symᵏ`; if k is even, every even m ≤ 3k occurs in the triple
  tensor. These are consequences of the existing full CG theorem and scalar
  arithmetic, not evaluated multiplicity tables.
- [ComplementaryExteriorDuality](../../../Math/RepresentationTheory/ComplementaryExteriorDuality.lean)
  proves an equivariant isomorphism `Λᵏ V ≅ (Λˡ V)*` when
  `k+l = dim V` and **the determinant of every group operator is one**.
  Naturality and invariance of the perfect wedge pairing are proved.
  This applies to the semisimple actions after proving their determinants;
  it does not discard a U(1) or residual determinant character.
- [BalancedExteriorWeights](../../../Math/RepresentationTheory/BalancedExteriorWeights.lean)
  proves the bound `min(n,D−n)` when a D-element eigenbasis has integer
  weights in [-1,1] with total weight zero. Both the selected subset and its
  complement bound the sum. The argument also handles above-capacity degrees
  through the empty exterior basis.
- [CompactHomSupport](../../../Math/RepresentationTheory/Characters/CompactHomSupport.lean)
  proves equality of the dimensions of `Hom(rho,sigma)` and `Hom(sigma,rho)`
  for finite-dimensional continuous complex compact-group representations,
  hence equivalence of their zero/nonzero support. Haar inversion and the
  existing Hom integral formula suffice; the integral is not numerically
  evaluated, and no Weyl torus-reduction input is used.

`TensorDeterminant.map` derives the determinant formula for a tensor action
from mathlib's matrix Kronecker identity. `InvariantVectorInjection` preserves
injectivity when tensoring with a normalized invariant vector. The relevant
symmetrization diagonal lemma is also registered in the persistent audit.

## Actual SM connections already proved

[SMGenerationCauchy](../../../Physics/StandardModel/Operators/SMGenerationCauchy.lean)
uses the color group and **three independent SU(2) factors** (weak, left spin,
right spin). Its inclusion in the existing combined compact model sets only
the U(1) component to one. `actual_quark` and `actual_lepton` identify the
resulting actual fields with three trivial-flavor copies of the constructed
one-generation carriers. The unused right spin factor is retained as an
independent factor; it is not identified with left spin.

The one-generation component maps are proved injective:

    Sym⁶ weak → Λ⁶ Q_generation;
    Sym³ weak ⊗ Sym³ leftSpin → Λ³ Q_generation;
    Sym² weak → Λ² L_generation.

The degree-one L component is an equivariant isomorphism. Color/spin volume
triviality is proved from determinants of the actual operators.

[SMGenerationSupport](../../../Physics/StandardModel/Operators/SMGenerationSupport.lean)
combines these with the independent-generation injections and the proved
spin invariant `omegaPower`. It constructs injective weak constituent maps:

| Three-generation exterior source | Range of constructed weak constituents |
| --- | --- |
| Q6 | every even m ≤ 6 |
| Q12 | every even m ≤ 12 |
| Q18 | every even m ≤ 18 |
| L2 | every even m ≤ 2 |
| L4 | every even m ≤ 4 |
| L6 | every even m ≤ 6 |

These are actual equivariant subrepresentation witnesses, including exterior
statistics. The subsequent [non-numerical consumers](non-numerical-support-results.md)
now connect all six families to actual local coefficients/kernels, reversing
Hom through proved continuous models and restoring hypercharge. They also
prove complete original-Higgs support iff statements for all positive L
degrees and Q degrees through 18, with existing scalar cyclic q/l actions.
This does not complete the full signed Q/L criterion.

[SMConstantWeakCapacity](../../../Physics/StandardModel/Operators/SMConstantWeakCapacity.lean)
already connects the sharp bound to **all ten actual signed species**, with
arbitrary supplied residual flavor representations. It proves

    m > min(n, speciesDimension−n)
      → every actual local coefficient is zero
      → the actual finite constraint kernel has dimension zero.

The field eigenbasis, balanced weight sum and constant-content exterior-source
equivalence are proved inputs to this result. It applies to the original local
gauge/Weyl action; neither a Weyl integration premise nor a computed matrix
rank is required. It is an upper-bound criterion, not a sufficient permission
condition. In particular no claim about a generated interaction or rate follows.

## Expansion and dependency boundary

The diagonal formula now lives in
[SymmetricMultilinearDiagonal](../../../Math/RepresentationTheory/SymmetricMultilinearDiagonal.lean).
The shared projection module is unchanged from the preceding commit. Both
Cauchy maps use the formula at a symbolic degree: the proof replaces a sum
of equal terms by its cardinality and cancels the factorial, without listing
permutations. Their SM consumers mark the map definitions locally
`irreducible` and use the proved naturality/injectivity statements. This is
an elaboration boundary; it does not change Lean's kernel or trust model.

The sharp capacity is defined by the cardinality of the actual `fieldBasis`
index. `field_dimension` identifies it with the actual field dimension;
`dimension_eq` recovers the existing ten-species dimension convention from
the previously proved `species_dimension`, rather than importing the rank
classifier. Constant patterns are defined directly. The original bound and
theorem hypotheses are preserved by these identities.

The persistent structural audits additionally reject numerical evaluator
imports and closed neutral certificates. In particular, this route does not
import `SMConstantContentRanks`, `LLHHKernelRank`, `SMGroupedCharacter` or the
Q18 arithmetic certificates. General coefficient/kernel equivalences and
structural dimension identities remain available. This boundary does not
claim that all historical dependencies avoid every small finite check, or
that a full project rebuild never executes the separately retained arithmetic
proofs. See the [verification record](structural-verification.md).

## Q18 middle-degree connection

The user-approved [Q18 replacement](q18-support-results.md) now connects the
Q18 constituent witnesses to nonzero actual coefficients/kernels, uniformly
for even m <= 18 at delta -6. It uses the proved middle exterior pairing,
with no analytic Hom reversal or evaluated character integral. Its exact
numerical predecessor is archived; this does not rederive its old dimensions.
The later [non-numerical consumers](non-numerical-support-results.md) now cover
the other lower-half families and their bounded original-Higgs/q/l iff.
The complete signed arbitrary-m support iff below remains open.

## Still open

1. The full proposed semisimple constituent iff at arbitrary m, independently
   of original Higgs admissibility, still needs its remaining necessities and
   complementary cases. Original-Higgs and admissible Q/L tests of both signs
   are closed by the later signed/mixed result.
2. Arbitrary mixed-content branching remains at the
   [recorded prerequisite](signed-mixed-stop.md). Eight selected mixed families,
   arbitrary mixed conjugation and chirality exclusions are already connected.
3. A full pattern/572-assignment classification still needs all its selected
   mixed-content obligations. Any use of the retained extracted integers keeps
   the existing Weyl input; it does not establish that input.

The proposed complete Q/L criteria in the assessment remain **unproved**.
The 107-row compiled table, the 572-assignment search and arbitrary mixed-content
classification have not been promoted to proved classifications by these adapters.
No new external theorem premise or dependency was introduced.

Persistent audits are `AuditStructuralExteriorSupport` and
`AuditSMStructuralSupport`; commands and final results belong in
[structural verification](structural-verification.md).
