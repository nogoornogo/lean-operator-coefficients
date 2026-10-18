# completed generalizations

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

## Completed Generalizations

Reusable representation-theoretic results were extracted in the order below. The
labels A-C refer to the generalization review, not the original SU(6)
embedding/hypercharge/standard-branch lemma labels. The completed scoped
Abelian selection-rule theorem remains the baseline; these mathematical
generalizations do not automatically enlarge its physical assumptions.
See [the Weyl model dossier](../../../proof/current/inputs/GUT/WEYL_MODEL.md) for that scope.

1. **A: character restriction obstruction (complete).**
   `Math/RepresentationTheory/Characters/CharacterRestriction.lean` proves conjugation-induced
   invariance and non-invariant-target exclusion for finite integer combinations
   of actual representations, using mathlib's `Representation.char_conj`.
   The generic API has no SU(6) imports. `Finsupp` coefficients over actual
   `FDRep` objects cover the full finite-virtual character image. The existing
   SU(6) presentations have a proved character-preserving adapter, and the
   flipped invariance/no-uplift proofs now use the generic API. Persistent
   audits include a permutation-group obstruction, signed realizable examples,
   and a counterexample to dropping evaluator faithfulness. Full build:
   4230 jobs; audited declarations use only the standard axioms.
   This is a necessary-condition obstruction, not a sufficient lifting test.
   Declarations, scope, and audit controls are recorded in the
   [character-restriction dossier](../../../proof/current/inputs/Math/CHARACTER_RESTRICTION.md).
2. **B: equivariant kernel/cokernel character index (complete).**
   `Math/RepresentationTheory/Characters/CharacterExact.lean` proves
   `chi(ker M) - chi(coker M) = chi(V) - chi(W)` for finite-dimensional
   representations over any field of any monoid, without unitarity or
   semisimplicity. It uses the pinned TauCeti exact-trace theorem twice and
   constructs the algebraic quotient action. A proved representation
   equivalence connects this quotient to the existing unitary orthogonal
   complement. Symmetric-mass dual-index conservation now needs no norm,
   inner product, or unitary-action hypothesis. Older signatures remain
   available as wrappers. Persistent audits include a nonsplit rational
   shear extension with indices +1 and -1. Full build: 4234 jobs; audited
   declarations use only the standard axioms.
   See [the exact-character dossier](../../../proof/current/inputs/Math/CHARACTER_EXACT.md) for the
   algebraic API, compatibility adapters, and nonsplit audit example.
3. **C: multiplicity spaces and centralizers (complete).**
   `MultiplicityCommutant` constructs finite-copy models on the actual
   isotypic components, proves choice-independent multiplicities, and
   identifies the commutant algebra with a product of full matrix algebras.
   `CommutantCentralizer` identifies the actual GL centralizer with their
   units. `UnitaryMultiplicity` constructs these models for arbitrary
   finite-dimensional unitary representations; the old SU(6) semisimplicity
   API now delegates to this generic proof. `MultiplicityMatrix` proves
   unitary compatibility and `prod det(A_i)^(n_i)` in block coordinates,
   with a continuous product action and closed determinant kernel.
   Persistent audits cover repeated constituents, the zero representation,
   and a weighted SU kernel with exactly two elements.
   `UnitaryIntertwiner` now proves equivariant polar normalization;
   `IsometricMultiplicity` constructs an isometric Hilbert multiplicity
   decomposition for every finite-dimensional unitary representation.
   `UnitaryCentralizerTransport` proves two-sided continuous U/SU centralizer
   transport to this model, preserving actual operator determinants.
   `HilbertMultiplicityOperator` and `HilbertMultiplicityDeterminant` now
   prove actual adjoint and weighted-determinant compatibility.
   `MultiplicityUnitaryCentralizer` identifies the full Hilbert commutant
   with scalar-mixing matrices and constructs the `product U(m_c)`
   topological equivalence. `MultiplicitySpecialCentralizer` identifies the
   SU centralizer with the full kernel of `product det(A_c)^(dim S_c)`,
   retaining finite components. `UnitaryMultiplicityClassification` derives
   both equivalences from the actual representation and unitarity alone.
   No model, exhaustion, or classification certificate is assumed.
   Persistent audits cover non-isometric input, zero/repeated constituents,
   a nontrivial permutation action, both continuity directions, and a
   nonidentity Hilbert operator retained by the weighted determinant.
   The algebraic dimension comparison is not assumed unitary.
   Verification: targeted audit 3606 jobs, full build 4255 jobs; audited
   declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
   The concrete `U(1)^2` theorem is preserved, not generalized by assertion.
   See [the multiplicity-centralizer dossier](../../../proof/current/inputs/Math/MULTIPLICITY_CENTRALIZER.md).

The requested reusable A-C roadmap is closed. Upstream extraction or a
classification of connected components of the weighted kernel would be
separate follow-ups, not missing hypotheses of these equivalences.
