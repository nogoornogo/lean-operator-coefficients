# Existing q/l SM Support Classification

- ID: `sm-ql-support-classification`
- Status: completed by the compact-kernel follow-up
- Result type: proved residual separation and exact finite-rank support predicate
- Working branch: `proof/sm-ql-support-classification`
- Integration target: `proof/sm-higgs-support-cutoff`
- Parent exception: bounded child of the unmerged finite-reduction topic;
  this child may merge back into that parent under the repository workflow.
- Authorization: user requested the existing q/l complete support extension.
- No master merge or remote push is authorized.

Master integration was authorized at stage 01 and includes this topic at
`checkpoint 01`; the original branch/parent target above remains historical. See
[merged-state verification](../sm-rank-certificates/verification.md#master-integration-at-stage-01).
No remote push was authorized or performed.

## Frozen endpoint

For the fixed three-generation signed SM/Higgs input, specialize the finite
Hom table to the existing cyclic q/l flavor action, at arbitrary positive
cyclic order k. Signed charges are [q,q,q,l,l,-q,-q,-q,-l,-l]. Higgs is
residual neutral. Classify every table entry's actual nonzero coefficient
support, retaining color, weak, hypercharge, Lorentz/Weyl and statistics.
New residual action classes, Higgs copies, derivatives, masses/VEVs, quantum
or UV realization and rates are excluded. Recounting the 572 assignments is
a separate consumer, not necessary for the classification theorem.

Complete means an explicit proved predicate without an unevaluated
invariant-Hom `Allowed` term. A charge-only criterion or reduction to local
gauge/Weyl Hom does not reach this endpoint.

## Ordered work and scope gate

1. Prove scalar-residual separation for the actual content source and each
   finite Higgs constituent. This closes the dependence on k,q,l exactly.
2. Inspect two routes for the remaining local invariant classifier:
   actual-group character/constituent counting, and exact finite matrix
   constraints justified by actual group generators and polynomial actions.
3. Construct and certify the local classifier only if its needed interfaces
   are already proved or bounded helpers within those interfaces suffice.
   Freeze any new theorem-level foundational prerequisite and stop for a
   scope decision before starting a separate foundational milestone.

Do not substitute Lie-invariant, torus-neutral, ordered-tensor, formal
character or sampled-matrix tests for actual statistical group invariants.
No missing correspondence may become an assumption of the complete result.
Keep pins and axiom policy unchanged. Verify any proof milestone with focused
builds, persistent strict audits and full lake build; check links/layout/diff.

## Result

The [residual separation result](results.md) passed focused/full builds,
strict audits and repository checks. The [two-route assessment](local-classifier-boundary.md)
reached the local-invariant-classifier scope gate and froze the required
actual group-to-finite-predicate connection before implementation.
The user subsequently authorized the
[finite matrix connection attempt](../sm-local-invariant-kernel/README.md).
That child proves generic kernel/rank and sampling interfaces plus actual
Weyl controls. The later
[compact-kernel completion](../sm-compact-kernel-completion/results.md)
discharges the remaining compact test obligations and replaces every retained
local `Allowed` term by an exact finite matrix-rank predicate.
The earlier [finite reduction](../sm-higgs-support-cutoff/results.md) remains
complete independently of this extension. Results and verification will be
recorded in [verification](verification.md).

## Starting sources

- [Finite table](../../../Physics/StandardModel/Operators/SMFiniteSupportTable.lean)
- [Actual q/l dictionary](../../../Physics/StandardModel/Operators/DuqlHiggsContent.lean)
- [Content adapter](../../../Physics/StandardModel/Operators/ContentHiggsSupport.lean)
- [Weyl group/action](../../../Physics/FieldTheory/Spinor/WeylSpinor.lean)
- [Compact Hom counting](../../../Math/RepresentationTheory/Characters/CompactHomDimension.lean)
- [Workflow and scope gate](../../architecture/WORKFLOW.md#endpoint-and-stop-gate)

## Subsequent statistical Weyl connection

The [statistical finite-kernel result](../sm-statistical-finite-kernel/results.md)
now identifies every actual local coefficient with finite Weyl rows plus
explicit actual gauge conditions, and composes this with the original all-degree
q/l iff. The [compact-kernel completion](../sm-compact-kernel-completion/results.md)
adds full gauge finite sampling. Rank enumeration and the 572 assignment
recount remain separate consumers.
