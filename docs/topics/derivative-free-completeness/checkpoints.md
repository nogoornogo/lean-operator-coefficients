# Historical Checkpoints

This preserves the successive frozen endpoints and their historical verification.
For the current scope and status, see [the overview](README.md).

# Derivative-Free Operator Completeness

- ID: derivative-free-completeness
- Status: in-progress
- Result type: algebraic completeness
- Working branch: `proof/derivative-free-completeness`
- Integration target: `refactor/selection-rules-paths`
- Parent exception: work starts on the user's current unmerged renamed layout;
  integration into master remains a separate user decision.

## Frozen First Endpoint

Construct an actual representation quotient by independently given linear
relations, prove its equivariant Hom universal property with explicit inverse,
and derive a residual-Hom presentation from finite local invariant contractions
and exchange matrices. The residual group and flavor modules are arbitrary;
finite dimensionality is not introduced. Local contractions must carry proved
normalization and completeness certificates. They are not discovered by this
theorem. Relations are specified on inputs, not defined as a coefficient image.

Recover the finite-generator completeness construction and a physical Weinberg
consumer; check empty, bosonic, fermionic and zero-quotient cases. Existing four
sector results and their independent field realizations remain valid consumers
of the previously proved statistics layer. Do not claim a uniform exterior
realization or full SMEFT enumeration.

## Milestones

1. General stable-relation quotient and equivariant Hom descent.
2. Arbitrary-flavor finite-local-coordinate relation module and residual quotient
   completeness, with extraction/reconstruction formulas.
3. Physical consumer, controls, persistent strict audits, documentation and
   full build. Commit verified checkpoints and continue to this endpoint.

## Subsequent Roadmap

The arbitrary-slot endpoint reuses pinned TauCeti tensor permutation actions:
prove commutation with arbitrary residual tensor powers, then instantiate the
finite statistics relation quotient for trivial/sign characters. Inspect the
existing Young idempotent and Schur-Weyl interfaces before building mixed types;
do not transfer their finite-standard-carrier statements to arbitrary flavors.

Resumed endpoint: for a finite statistics group acting linearly and commuting
with the arbitrary residual group, prove the relation quotient equivalent to
the invariant subrepresentation by averaging. The statistics-group cardinal
must be invertible in the scalar field; no dimension or compactness premise
is allowed. This establishes the finite-group symmetric-component foundation,
not general mixed Young types or permutation tensor actions of all degrees.

The next resumed endpoint is carrier-level comparison of the two-slot Young
components with independently defined symmetric and exterior squares, using
their existing universal properties. Prove both inverse laws and equivariance,
with pure-tensor normalization formulas and persistent audits. Continue on
the recorded branch; no new dimension, topology or literature premise is allowed.

The user resumed formalization after the first-stage checkpoint `checkpoint 01`.
The next bounded endpoint, on the same branch, is the two-slot (S2) Young
splitting: for an equivariant involution over C, prove signed projectors,
an actual equivariant equivalence from the signed relation quotient to its
eigenspace, and a symmetric/antisymmetric product decomposition. No finite
dimension is required. Verify signs and inverse laws with persistent audits.
This is a first Young foundation, not the general partition/Schur theorem.

After this endpoint, finite-flavor symmetric-group actions and Young/Schur
decomposition can support p-basis refinement. Then bounded y/m constructions
and basis conversion precede a separate derivative/EOM/IBP/amplitude project.
j-basis requires a specified channel and Casimir interface. These stages are
not acceptance requirements of the first theorem and are not silently opened
as foundational prerequisites.

## Result

The frozen first endpoint is proved. Stable input relations give an actual
quotient representation and inverse Hom descent/pullback. Finite local
contractions and exchange matrices give explicit residual quotient Hom
coordinates, with extraction, reconstruction and a nonzero equivalence.
The independently defined Weinberg `ModelSector` is a consumer, and its Hom
comparison agrees with the existing symmetric-square classification. Empty
relations, both statistics signs and inconsistent identity signs have proved
controls. See the final [proof dossier](../../proof/current/core/Math/RELATION_COMPLETENESS.md).

The [two-slot Young extension](two-slot-young.md) is also proved: the signed
quotient is now equivalent to the actual signed eigenspace, the two components
give an equivariant product decomposition, and tensor-slot exchange supplies
the shapes (2) and (1,1). There is no dimension premise.

The carrier-adapter extension is proved as well: the signed components and
relation quotients are equivariantly equivalent to the independent symmetric
and exterior squares. Tensor square splits into their product, with normalized
generator formulas in both directions. See the
[two-slot result](two-slot-young.md#independent-square-carriers).

This closes the first algebraic stage and its S2 extension, not the complete Li basis program.
Subsequent stages remain the roadmap above; no new prerequisite or physical
scope expansion was needed. Other sector-specific quotient adapters are not
claimed here.

## Scope And Stop Conditions

Li et al. motivates the quotient/statistics and basis roadmap; no paper theorem
is an assumed Lean premise. See the existing
[literature comparison](../operator-completeness-interface/README.md#relationship-to-li-et-al).
No matching, rates, RGE or numerical dynamics is added. Pins and axiom allowlists
remain unchanged. Stop on a counterexample to the frozen quotient statement or
an essential new premise beyond equivariance and proved local completeness.

## Verification

Verified on the pinned toolchain, stage 01:

- `lake build Math.RepresentationTheory.Audit.AuditRelationCompleteness
  Physics.StandardModel.Operators.Audit.AuditWeinbergRelationCompleteness`:
  passed, 24 + 9 strict transitive axiom checks; standard Lean axioms only.
- `lake build`: passed, 6,261 jobs, no warnings or errors.
- `node tools/layout/check-layout.mjs`: passed, 1,023 modules, including
  layer/import/cycle/aggregate and relocation audits.
- `node tools/docs/check-links.mjs`: passed, 378 documents, no broken links.
- `git diff --check`: passed.

No dependency pins or audit allowlists changed. No merge is authorized.

The resumed S2 extension was verified at stage 01:

- `lake build Math.RepresentationTheory.Audit.AuditTwoSlotYoung`: passed,
  16 additional strict transitive axiom checks.
- `lake build`: passed, 6,264 jobs, no warnings or errors.
- Layout checks: passed, 1,026 modules.
- Documentation links: passed, 379 documents, no errors.
- `git diff --check`: passed.

The carrier adapters were subsequently verified:

- Focused audit: 36 two-slot checks, including both square inverse laws and
  the three explicit splitting generator formulas.
- Full build: 6,265 jobs, no warnings or errors.
- Layout: 1,027 modules, passed. Links: 379 documents, no errors.
- `git diff --check`: passed. No pins or axiom allowances changed.

Next mathematical milestone: larger symmetric-group representations. General
partition-labelled Young/Schur decomposition and p/y/m/j-bases remain unproved.

## Finite Statistics Extension

The resumed finite-group endpoint is proved in
[FiniteStatisticsQuotient](../../../Math/RepresentationTheory/FiniteStatisticsQuotient.lean).
For a commuting finite statistics action, its relation quotient is equivariantly
equivalent to its invariant subrepresentation. The map is normalized averaging;
its inverse is quotient inclusion. Inverse character twists provide character
components, with the original-action eigencondition proved. The scalar field
is arbitrary provided the finite group's cardinal is invertible. Residual
group and carrier dimension remain arbitrary.

This is not a construction of arbitrary tensor-slot permutation actions, mixed
Young components or a basis enumeration. Those remain next milestones.

Verified stage 01:

- Focused build of `Math.RepresentationTheory.Audit.AuditFiniteStatisticsQuotient`:
  13 strict transitive axiom checks, standard axioms only.
- `lake build`: 6,267 jobs, no warnings or errors.
- Layout: 1,029 modules; links: 379 documents, no errors.
- `git diff --check`: passed. Pins/allowlists unchanged; no merge authorized.

## Arbitrary-Slot And Mixed-Projector Checkpoint

[The arbitrary-slot milestone](arbitrary-slot-young.md) is proved. Every degree
has actual tensor permutation statistics compatible with arbitrary residual
action, with symmetric/sign relation quotient equivalences. Each specified
mixed Young tableau yields an equivariant normalized idempotent, a stable
kernel and image, their complement theorem, and a kernel-quotient/image
equivalence. Normalization is proved upstream and audited transitively.

Verified stage 01: focused audit 14 strict checks; full `lake build` 6,299
jobs, no warnings/errors; layout 1,032 modules; links 380 documents, no errors;
`git diff --check` passed. No pins or allowlists changed; no merge authorized.

The overall basis roadmap remains in progress. The next obligation is a
nonredundant isotypic/multiplicity decomposition compatible with the local
contraction action, not an unsupported direct sum of all tableau images.
The complex Specht and universe-safe simple-module class interfaces are now
connected; the earlier rational-only inspection was incomplete.
General p/y/m/j-bases and derivative/EOM/IBP stages are not completed.

## Intrinsic Isotypic And Partition Coordinates

[The isotypic extension](isotypic-residual.md) proves a nonredundant direct-sum
equivalence for commuting finite statistics and arbitrary residual actions.
Residual Hom becomes a product of block Homs, with explicit restriction and
inverse reconstruction. Tensor powers in every degree are covered without
finite-dimensional flavor. Their distinct components are labelled injectively
by complex Specht partitions; supported-partition coordinates are an actual
linear equivalence. These are intrinsic block coordinates, not a basis chosen
inside each multiplicity space.

Stable-relation quotients also admit this decomposition when the relation space
is stable under both actions. Statistics stability is an explicit application
condition, not a consequence of residual stability alone.
