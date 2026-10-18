# E6 Endpoint-First Plan

Archived checkpoint; not a current work queue. Consult the current topic records.

**stage 02 update:** the user approved the
[literature-assisted topology boundary](../../../proof/current/inputs/GUT/E6_LITERATURE_BOUNDARY.md).
It leaves the physical theorem unchanged and does not restart the foundational
route below. Simple connectedness is conditional in Lean; named-E6 interpretation
uses separately recorded external classification.

Updated: stage 01

## Decision

The user closed E6-0 as a feasibility phase and redirected work toward
the supported selection-rule theorem. At that checkpoint all checked
E6-0b through E6-0p proofs were preserved, while E6-0q, exact center,
simple connectedness and general global-form construction were deferred.
They are not conditions for completing
the audit. No new Lean result was asserted by that planning change.

After the candidate's actual-model milestone, the user requested progress
on the remaining global obligation. The separately bounded
[center/quotient package](../../../proof/current/inputs/Math/E6_CENTER_THREE.md) now closes the concrete
order-three scalar step and non-descent of the actual 27 to the center
quotient. The next bounded [cubic package](../../../proof/current/inputs/Math/E6_CUBIC_CENTER.md), requested
in a further continuation, proves the exact order-three center through
actual group invariance. Simple connectedness and the global identification
remain unproved. A further bounded [torus package](../../../proof/current/inputs/Math/E6_COMPACT_TORUS.md)
constructs the actual maximal torus and exact Cartan period lattice,
without computing the candidate's fundamental group. These results do not
restart E6-0 or authorize a
recursive foundation sequence.

The audit found useful local/matrix foundations, not a ready-to-use concrete
compact E6 endpoint. That is a valid audit outcome; completing all missing
foundations is a separate project requiring explicit approval.

## Frozen Target and Actual Dependencies

The primary conclusion remains: under the existing ordinary Abelian action,
finite-dimensional unitary source, invariant symmetric mass and exact light
dual target hypotheses, not every supported physical Delta B = 1 signature
can be forbidden. No nonzero amplitude, finite lifetime or exact SM vacuum
is asserted. The mass target remains an explicit model hypothesis, not a
new dynamical theorem.

The existing [StandardChain](../../../../GUT/Common/StandardChain/StandardChain.lean)
already proves this conclusion in `Model.selection_rule_obstruction`.
Source inspection for this plan confirms:

| Interface | Actual inputs relevant here | Not an input |
| --- | --- | --- |
| `Model i rho` | Actual `SU(5) ->* G`, unitary product action, invariant mass, finite profiles/singlets and exact light target | Center order, simple connectedness, a Spin intermediate group |
| `ContinuousModel i rho` | The preceding inputs plus inclusion injectivity/continuity and continuous action | Global Lie-group classification |
| Concrete named E6 application | A justified actual carrier and compatible inclusion, not assumed as a certificate | Automatically proving every property in the earlier construction contract |
| Positive-target 27 example | Actual oriented group restriction and target derivation | Merely counting 27 weights or postulating the target |

This separates **theorem inputs**, **global identification needed for the
name of a concrete application**, and **one particular construction route**.
A result for `compactIdentityComponent` alone is a candidate-group result;
it does not settle the intended global E6 identification. That boundary
cannot be erased to make the endpoint appear complete.

## One Direct-Bridge Decision

**E6-ENDPOINT-1 is complete as a decision.** At that checkpoint implementation
was deferred. The subsequently user-approved
[finite coordinate comparison](../../../proof/current/applications/GUT/E6_SU5_COORDINATES.md) is now complete:
actual module equivalence, generator actions and Hermitian compatibility.
The separately approved [group-map package](../../../proof/current/applications/GUT/E6_SU5_GROUP_MAP.md) is also
complete: actual continuous injective inclusion into the candidate,
represented-exponential compatibility, subgroup membership and group-level
intertwining. The common conditional consumer is checked in its audit.
The later bounded [positive-target model](../../../proof/current/applications/GUT/E6_POSITIVE_TARGET.md) is also
checked on the candidate, using zero mass and trivial residual action.
Global E6 identification remains unproved. The original decision and its
stop boundary remain historical.
The [result](../decisions/E6_DIRECT_BRIDGE_DECISION.md) records the first missing
coordinate/action comparison shared by the two inspected routes at that time.
The original bound below is retained to document the stopping decision:
a single investigation pass over at most these two routes, using pinned/local sources only.

1. An explicit SU(5) action on the 27 coordinates, with proved preservation
   of the existing matrix algebra and actual membership in its connected
   compact candidate. Reuse existing SU(5) representations/generation APIs
   where they fit; no general Lie integration is authorized.
2. Reuse the already constructed Spin(10) actions only if the missing
   concrete matrix compatibility gives the same finite SU(5) bridge without
   a new global-integration or center-classification project.

Acceptance for this decision is either a source-supported finite proof
package or a named first unavailable bridge and deferral. Do not spend
another series of audit milestones proving prerequisites of the decision.
The existing common theorem must not be duplicated as a new conditional
E6 wrapper with an assumed inclusion.

An implementation package, if the decision supports one, is limited to:

- an explicit group action/map on the specified carrier;
- membership and continuity/injectivity, with no assumed compatibility;
- specialization of the existing selection-rule theorem, stating exactly
  which carrier is covered and which named-E6 identification is still open.

List the intended modules, dependency edges and focused checks before
implementation. Ordinary local helpers inside those interfaces are allowed;
a prerequisite requiring new general Lie integration, fundamental-group,
reductive or classification theory ends this package. Do not replace it by
the previously deferred center sequence. Report and seek approval before
any foundational expansion. All work must obey the
[endpoint/stop gate](../../../architecture/WORKFLOW.md#endpoint-and-stop-gate).

The actual SU(5) restriction of the 27 is proved by the group-map
intertwiner. The separately approved model package now derives its exact
positive dual light target for all torus/residual-invariant symmetric
masses and constructs a zero-mass continuous inhabitant. All 27 modes
remain light in that example; its full character is not the 17-dimensional
SM plus two singlets. The Spin(10) module identification is not asserted.
The original Spin-based E6-1/2 plan remains a deferred alternative. Existing
SU(N), Spin and symplectic endpoints do not depend on completing either route.

The original decision pass did not establish this implementation package.
The later coordinate and actual-map implementations were separately scoped
and checked. Both stop at their stated deliverables; neither authorizes
renewed global foundations or a silent expansion into general integration.

## Preservation and Verification

The pre-coordinate baseline was `checkpoint 01`, E6-0p. Current proof and full-build
results are kept in [Historical milestones](../../proof-program-context/checkpoints/README.md). Future packages
require focused standard-axiom audits, full regression and a milestone
commit, while keeping all previous proofs and dependency pins intact.
