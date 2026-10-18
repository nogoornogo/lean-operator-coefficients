# Actual Local Invariants And Finite Matrix Kernels

- ID: `sm-local-invariant-kernel`
- Status: completed by downstream finite-test topics
- Result type: proved generic matrix connection; downstream topics complete the fixed-input connection
- Working branch: `proof/sm-local-invariant-kernel`
- Integration target: `proof/sm-ql-support-classification`
- Parent exception: bounded child of that unmerged topic, never master.
- Authorization: user requested a plan followed by formalization through
  its stop condition at stage 01.
- No master merge or remote push is authorized.

Master integration was authorized at stage 02 and includes this topic at
`checkpoint 01`; the original branch/parent target above remains historical. See
[merged-state verification](../sm-rank-certificates/verification.md#master-integration-at-stage-01).
No remote push was authorized or performed.

## Contract

For the actual statistical local representations in the q/l finite Higgs
table, construct a specified finite constraint matrix and a linear
equivalence between its kernel and the actual invariant coefficient space.
The matrix may be symbolic and large; no enumeration of the full universe
is required. Its entries and exhaustiveness must be proved, not inferred
from sampled elements, a torus test or a Lie kernel.

The [plan](plan.md) fixes rows, coordinates, actual-group route, prerequisites
and stopping conditions. The previous [q/l separation](../sm-ql-support-classification/results.md)
remains a distinct verified checkpoint.

## Work

The [results](results.md) prove the exact finite-kernel consumer, rank
criterion, polynomial sampling/grid tests, actual Weyl generation and an
unconditional one-spinor finite-kernel control. The planned stop is reached
at actual SU(3) plane-family generation. Its group-decomposition certificate,
the actual statistical polynomial identities and coordinate construction
remain explicit obligations, not theorem assumptions of a claimed complete
SM result. No general classical-group foundation was started.

## Verification

Proof work and checks are recorded in [verification](verification.md).

## Starting sources

- [Local classifier boundary](../sm-ql-support-classification/local-classifier-boundary.md)
- [q/l coefficient consumer](../../../Physics/StandardModel/Operators/QLFiniteSupport.lean)
- [Actual Weyl action](../../../Physics/FieldTheory/Spinor/WeylSpinor.lean)
- [Finite invariant factor](../../../Math/RepresentationTheory/FiniteInvariantFactor.lean)
- [Workflow](../../architecture/WORKFLOW.md)

## Follow-up SU(3) prerequisite

The authorized [plane-generation child](../su3-plane-generation/README.md)
now proves actual SU(3) algebraic generation, with an explicit three-plane
factorization. This closes the generating-family prerequisite described in
this checkpoint. Statistical-source parameter identities, finite sampling
and coordinate descent were then supplied by the linked downstream topics.

The subsequent [statistical-kernel child](../sm-statistical-finite-kernel/results.md)
closes paired-Weyl polynomial identities and statistical descent for all
contents. The later
[compact-kernel result](../sm-compact-kernel-completion/results.md) supplies
exact fixed-circle tests and instantiates this matrix interface for the full
actual local group.
