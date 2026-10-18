# Uniform Finite SM/Higgs Support Reduction

- ID: `sm-higgs-support-cutoff`
- Status: completed
- Result type: proved uniform finite reduction with residual parameters
- Working branch: `proof/sm-higgs-support-cutoff`
- Integration target: `master`
- Authorization: user requested this plan and a new branch at stage 01.

Master integration was authorized at stage 02 and includes this topic at
`checkpoint 01`; the original branch/parent target above remains historical. See
[merged-state verification](../sm-rank-certificates/verification.md#master-integration-at-stage-01).
No remote push was authorized or performed.

## Endpoint And Scope

Prove a uniform finite reduction of all-degree support for the existing
single neutral-residual SM Higgs doublet/dual and the fixed three-generation
signed fermion input. Preserve the supplied species flavor representations
of a residual group H as parameters. The finite tests remain actual
full-group invariant coefficient spaces, with their `Allowed` predicates
unevaluated. This is not complete support classification.

The [plan and contract](plan.md) specify the finite predicate, source
statistics, phases, acceptance gates and stop conditions. No new residual
group classes are classified. Deciding the remaining Hom tests for existing
q/l actions is a separate possible project requiring a later user decision.

## Deliverables And Acceptance

1. A proved weak torus support bound for statistical fixed-content sources
   of the actual signed input and their duals.
2. Vanishing of source/weak-constituent coefficients above that bound.
3. An original-carrier support iff over a degree-independent finite test
   table, first for one nontrivial weak content and then for every content.
4. Proved stabilization along addition of a Higgs/dual pair, including a
   precise threshold, and connection to the finite fermion universe.
5. Registered sources, persistent strict axiom audits, assumptions/proof
   documentation, focused and full builds, layout/link/diff checks.

The finished theorem must construct the actual source and content transports;
no missing weight-bound, constituent-support, or spanning certificate may be
inserted as an extra premise of the fixed-input endpoint.

## Work And Open Obligations

The user authorized implementation through the stop condition. The source
bound, statistical-content connection, bounded constituent iff, finite
universe and stabilization are implemented. The [result](results.md) records
the exact statements and controls. The focused and full builds, strict audits
and repository checks passed. This reaches the selected endpoint; no new
foundational prerequisite or scope stop arose. Classifying `Allowed(T)`
requires a later user decision and is not remaining work for this topic.

Existing per-degree Higgs decomposition and full-field transport are proved
in the [preceding connection](../sm-support-and-lfv-decomposition/full-higgs-connection-results.md).
The new endpoint adds a source bound and uniform finite truncation; these
were not consequences already certified by that per-degree connection.

## Result And Verification

The finite reduction leaves `Allowed(T)` unclassified, as authorized.
The [dossier](../../proof/current/applications/Physics/SM_FINITE_HIGGS_SUPPORT.md)
links the public consumers. [Verification](verification.md) separates the
planning-only milestone from proof checks and completion evidence.

## References

- [Existing support topic](../sm-support-and-lfv-decomposition/README.md)
- [Full Higgs connection](../sm-support-and-lfv-decomposition/full-higgs-connection-results.md)
- [Finite fermion universe and preceding results](../sm-support-and-lfv-decomposition/results.md)
- [Workflow](../../architecture/WORKFLOW.md)
