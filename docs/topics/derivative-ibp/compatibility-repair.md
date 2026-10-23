# Initial Compatibility Repair Result

The subsequent [carrier/projection pilot](carrier-pilot.md) supersedes the
consumer stops below. This record retains the earlier checkpoint evidence.

The initial authorized workaround pass resolves the dependency name collision and the
triple-generation injection itself. It does not close the full-project gate.
At this checkpoint the candidate branch remained unmerged; dependency pins
were unchanged.

## Retained Changes

| Boundary | Repair and verified scope |
| --- | --- |
| Physlib/TauCeti symmetric names | Import the Physlib exterior module directly. Adapt symmetric sections D/E under `Math.PhyslibSymmetric`, omitting the colliding functoriality/product sections. Twelve strict checks and the Math aggregate pass together with TauCeti. |
| Triple-generation injection | `SMGenerationSupport.generation_triple` constructs and proves injectivity before specializing the field action. Q18/L6 consume the abstract result; their existing statements and hypotheses are unchanged. A separate strict audit covers eight generation-injection declarations. |
| Later generation consumers | Q18 coefficient support and lower-generation coefficient support still hit elaboration recursion limits. Passing the injection does not certify these consumers. |
| ScalarBlock | Still fails at the original radical-membership rewrite. Alternative mass-form/function interfaces did not pass default kernel checking and are removed. |

The [symmetric fragment](../../../Math/LinearAlgebra/PhyslibSymmetricDerivations.lean)
retains the pinned upstream copyright, authors and Apache-2.0 notice. Its
borrowed definitions/proofs are exactly sections D/E of the source registered
in [references](references.md#l1--external-physlib-snapshot), with a namespace
wrapper, root namespace opens and explicit representation-function calls.
A comparison reversing those qualification changes confirmed the retained
fragment matches the upstream source. No installed dependency was edited.
The imported Physlib closure is deliberately limited to the exterior module;
this does not repair arbitrary downstream imports of upstream symmetric code.

The [connection audit](../../../Math/Audit/AuditPhyslibAlgebraConnection.lean)
requires the exterior module, local fragment and TauCeti functoriality to be
co-imported. It retains the same six exterior and six symmetric obligations,
the same semiring/module generality and the existing axiom policy. The
[generation audit](../../../Physics/StandardModel/Operators/Audit/AuditSMGenerationSupport.lean)
checks the new helper and existing Q/L injections independently of the blocked
coefficient consumers. Both audits are registered in their layer aggregates.

## Failed Alternatives And Current Boundary

The source generation injection now builds without increasing recursion or
heartbeat caps. Checking its descendants exposed independent conversion costs
at `SMQ18Support.semisimple_allowed` and `SMLowerGenerationSupport.quark_local`.
Concrete composition/existential wrappers, local additive/module instance
aliases, restricted simplification, explicit map reconstruction and the existing
transparency option did
not close these consumers. Those trial edits are removed.

For ScalarBlock, an abstract radical lemma from equality of bilinear forms
passed. Specializing it through the concrete mass/equivalence presentation
still timed out in the kernel. Linear/function views, action certificates and
abbreviations did not close the gate; the last model trial failed at default
kernel checking after about 87 seconds. No larger cap was requested or
retained, and the failed helper/model/consumer edits are removed.

Expression inspection exposes different additive-group/monoid instance paths
in the inferred and presented types. That is evidence of a conversion boundary,
not a proof of an asymptotic complexity claim or a mathematical obstruction.
Further work needs a consistent additive/module presentation across the actual
source, representation equivalences and coefficient consumers. The current
pass does not introduce that broader representation refactor, weaken the
statements or disable any consumer/audit.

## Verification

- `lake build Math.Audit.AuditPhyslibAlgebraConnection Physics.FieldTheory.Mass.EquivariantWeylMassTransport`:
  passed (3723 jobs); 12 strict connection checks. The temporary generic mass
  helper in that run was subsequently removed after failed specialization.
- `lake env lean Physics/StandardModel/Operators/SMGenerationSupport.lean`:
  passed without diagnostics after the abstract generation repair.
- `lake build ... Math` in the combined focused run: Math target passed;
  the combined run failed on the concrete mass trial and generation consumers.
- `lake env lean Physics/StandardModel/Operators/Audit/AuditSMGenerationSupport.lean`:
  passed; 8 strict transitive checks, no diagnostics beyond the success report.
- Final full-build and repository gate results are recorded below. Earlier
  passing individual targets are not substituted for a full baseline.

The larger external SM jet and analytic IBP packages, derivative/IBP
completeness, optional doc-gen4 execution and HTML generation remain outside
this result. No master merge or push is performed.

### Final Gates

`LEAN_NUM_THREADS=4 lake build` completed with exit 1 and exactly these failing
targets:

- `GUT.SU6.Adapters.StandardScalarBlock`: original membership rewrite fails.
- `Physics.StandardModel.Operators.SMQ18Support`: recursion limit at the
  constituent-to-coefficient consumer.
- `Physics.StandardModel.Operators.SMLowerGenerationSupport`: recursion limit
  while connecting the Q18 constituent to the local coefficient consumer.

The connection audit passed 12 strict checks and the independent generation
audit passed 8 in that full run. Math is compatible with the selected narrow
connection. The Physics/GUT aggregates and the existing structural-support
aggregate audit remain blocked by the listed consumers; no upgraded full-build
baseline is accepted. Trial edits to the failing consumers were removed, and
the final sources match the failed-build snapshot at those boundaries.

Repository gates passed: layout (2077 modules), local links, topic index (148
topics with outcomes), portable metadata and `git diff --check`. The remaining
warnings include the earlier inferred-proposition `defProp` diagnostic and
module-system import recommendations, including the adapted fragment. No
linter, axiom or import policy was relaxed.

This partial repair was retained on `audit/derivative-ibp-physlib-435` without
parent/master integration, push or branch deletion. Its source injection alone
was not a completed coefficient connection. The later carrier/projection pilot
above supersedes that consumer boundary.
