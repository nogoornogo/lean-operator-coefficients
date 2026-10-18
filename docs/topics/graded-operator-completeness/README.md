# All-Degree Coefficient-Space Decomposition for Derivative-Free Operators

- ID: `graded-operator-completeness`
- Status: completed
- Result type: degree-uniform algebraic completeness equivalence and zero/nonzero iff
- Working branch: `proof/graded-operator-completeness`
- Integration target: `master`
- Integration evidence: Git ancestry against `master`; integration explicitly authorized after completion.

## Endpoint And Scope

Construct a degree-uniform, purely algebraic completeness theorem for invariant
coefficient functionals on exterior fermion and symmetric boson carriers.
For specified engineering degree and additive charges, identify the independently
defined coefficient space with residual-Hom factors constructed from the field
representations and their exchange relations. Prove inverse extraction and
reconstruction, total prohibition and existential nonzero criteria.

Residual groups are arbitrary abstract groups, and multiplicity representations
need no topological structure or continuity assumptions. No
finite-dimensionality, compactness or semisimplicity of the residual action
is assumed. Bose/Fermi statistics means algebraic exchange signs and symmetry,
not statistical inference, sampling or numerical processing. All proofs must
be checked in Lean; external basis generators are not prerequisites.

This succeeds the completed [dimension-seven BNV topic](../bnv-bounded-completeness/README.md).
Its dimension-eight-to-eleven individual extensions are not pursued. The new
goal is a coefficient-space decomposition theorem, not an unproved claim of their explicit classification.

## Deliverables And Acceptance

See the [frozen target and staged plan](plan.md). Required outputs are:

1. Arbitrary mixed-degree, species-supported input and charge/weight selection.
2. Constructed gauge-coinvariant and exchange-quotient residual representations,
   with natural, two-sided Hom equivalences and no spanning-dictionary premise.
3. Fixed-charge bounded products and all-degree prohibition/allowance iff.
4. Explicit comparison with the existing dimension-six/seven BNV equivalence,
   plus small multi-boson regression examples and persistent strict audits.

Completion requires all four groups, focused and full builds, layout/link checks,
and a completed-result proof dossier. A definition of the original space as its
own Hom, or a conditional unproved local dictionary, does not satisfy the gate.

## Result

All four acceptance gates A–D are complete. For every natural mixed degree,
species-supported invariant coefficients are linearly equivalent to products
of `Hom_H(Q_c,ℂ)` on constructed carriers
`Q_c = ((L_c)_G ⊗ M_c) / R_exchange`. Selected support, positive-weight bounded
contents, all-degree functional products and prohibition/nonzero iff are proved.
Actual SM/Higgs input comparisons with the existing six/seven classifications
commute with extraction and reconstruction. Two-boson and mixed-statistics
regressions are strict Lean theorems. See [results and boundaries](results.md).

Completed-result dossiers:
[coefficient-space decomposition theorem](../../proof/current/core/Math/GRADED_OPERATOR_COMPLETENESS.md) and
[actual SM comparison](../../proof/current/applications/Physics/GRADED_BNV_COMPARISON.md).
There are no remaining tasks within the frozen scope. No arbitrary-H decision
algorithm, finite all-degree cutoff, inevitable BNV or explicit dimension-eight-
to-eleven basis enumeration is claimed. Root README and dependency pins were
unchanged by this topic at its completion; later documentation topics made the
coefficient-space decomposition theorem the README's main claim.

## Verification

These are the original topic checkpoint counts, not the current repository's
module/job totals. They are retained as historical verification evidence.

- Focused endpoint build: 3,402 jobs, successful.
- Strict transitive checks: 84 mathematical and 16 actual SM comparison declarations;
  only `propext`, `Classical.choice` and `Quot.sound` are allowed.
- Full `lake build`: 6,518 jobs, successful, without warnings or errors.
- Layout: 1,191 modules; layers, imports, cycles and aggregate coverage pass.
- Documentation links: 454 Markdown files / 3,035 links / 100 heading fragments,
  zero errors; `git diff --check` passes.

Commands are recorded in [results](results.md). Master integration was explicitly
authorized after completion; Git ancestry records integration, and the historical
working branch name remains in this record after local branch cleanup.

## Checkpoint Records

These notes retain their historical checkpoint boundaries; the final result above
supersedes their then-open obligations:

- [Local coinvariants](local-coinvariants.md)
- [Mixed power descent](mixed-descent.md)
- [Mixed species projections](mixed-species.md)
- [Typed assembly and grading foundations](typed-assembly-and-grading.md)
- [Content indexing and separated quotient](content-and-intrinsic-descent.md)

## References

- [Plan](plan.md)
- [Mixed input and arbitrary-degree coefficient definition](../../../Math/RepresentationTheory/MixedWeightSupport.lean)
- [Relation quotient and inverse Hom descent](../../../Math/RepresentationTheory/RelationQuotient.lean)
- [Finite exchange quotient](../../../Math/RepresentationTheory/FiniteStatisticsQuotient.lean)
- [Existing arbitrary-slot framework](../derivative-free-completeness/README.md)
- [Completed seven-dimensional theorem](../../proof/current/applications/Physics/BNV_SEVEN_COMPLETENESS.md)
