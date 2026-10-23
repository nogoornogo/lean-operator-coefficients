# Model, Literature And Artificial-Case Validation Plan

This is the frozen acceptance matrix. Its discharged cases and exact evidence
are recorded in [validation results](literature-validation.md); the matrix
itself does not imply paper-wide validation. Each case names its model and role.
Keep commands and outcomes in this topic. The cross-topic literature ledger
receives only verified source-location comparisons after implementation.

## Constructed Model Consumers

| Named case | Reused source | Required new check |
| --- | --- | --- |
| SU(6) boundary amplitudes | [Chiral selection](../../../GUT/SU6/Boundary/ChiralSelection.lean), [interactions](../../../GUT/SU6/Boundary/Interactions.lean), [protection](../../../GUT/SU6/Boundary/Protection.lean) | Construct the shared correspondence from the existing maps and exactness results. Recover the SM gauge/residual dictionary and the same internal boundary tensors and coefficient claims. Retain the neutral sterile amplitude separately from the ten-species SM/Higgs coefficient alphabet. |
| Four-dimensional lepton-parity mass kernel | [Actual three-generation construction](../../../Physics/StandardModel/Spectrum/Representations/InverseCyclicSMRealization.lean), [Yukawa consumers](../../../Physics/StandardModel/Operators/Selection/InverseCyclicSMYukawa.lean) | Build the same shared API from the actual mass radical and its proved equivalence. Preserve the spectator mass, generation multiplicities, signed physical-field dictionary, nonzero Yukawa tensors and existing B1 input. No SU(6) lift is inferred. |
| Complete local scalar/Weyl density | [Yukawa model](../../../Physics/FieldTheory/Jets/Lagrangian/YukawaModel.lean), [standard density action](../../../Math/RepresentationTheory/Lagrangian/StandardDensityAction.lean) | Exercise the adapters on the complete density and full generated relation module. Prove evaluation/roundtrip compatibility; verify cancellations and the actual covariance hypotheses. Do not substitute a union of termwise equation ideals. |
| Nonabelian retained action | [Existing S3 samples](../../../Physics/StandardModel/Operators/BaryonOne/Qque/S3QqueTensorSamples.lean) | Instantiate an appropriate shared field/action constructor on one supplied nonabelian sample, without a hidden `CommGroup` requirement. Preserve the selected qque domain and its existing flavor-map boundary. |

For each main model, record a before/after inventory: input fields, caller
proof obligations, derived facts and remaining model-specific premises.
Acceptance requires actual reuse across the boundary and mass-kernel
mechanisms, not two wrappers that assume their final target equivalences.
No source theorem is weakened to simplify the comparison.

## Negative And Structural Controls

| Named control | Expected mathematical behavior |
| --- | --- |
| Proper target inclusion | A target embeds and has a left inverse but omits a selected component. The exact correspondence criterion fails its other inverse law. |
| Incorrect conjugate map | A supplied map uses the wrong character or Weyl convention. Exhibit failure of its required intertwining identity; do not assert a universal inequivalence without proof. |
| Extra light pair | A chiral-index match coexists with extra selected fields. The exact field dictionary rejects identifying that source with the smaller target. |
| Noncommuting selectors | Common selected spaces remain meaningful. A concrete small example refutes replacing their intersection by the image of the product without commutation. |
| Symmetry-breaking interaction | A chosen tensor is not invariant under the proposed retained action. It cannot supply an invariant-interaction or density certificate. |
| Invariant vacuum substitution | Invariance descends at a fixed vacuum; a deliberately nonfixed vacuum fails the stated factory condition. |
| Mixing destroys a proposed light space | Reuse [LightInheritanceBoundary](../../../Physics/FieldTheory/Mass/Algebra/LightInheritanceBoundary.lean): equivariant inclusion and agreement of restricted masses do not prove survival in the full mass radical. |
| Scalar-neutral nonzero control | Preserve a genuine allowed coefficient/tensor after removing the detecting action, rather than proving only zero-space examples. |
| Full-relation selection | Check the exact preimage of full relations and evaluation agreement. A selected free coefficient is not asserted to extend globally or survive arbitrary interacting EOM. |
| Total-density cancellation | Opposite terms cancel before Euler generation. The adapter follows the summed density and its resulting relations. |

Derive families from structural lemmas. Small explicit counterexamples may
check their own supporting identities; they do not replace the shared proofs
with finite tables, generated rank certificates or many component expansions.

## Literature Comparison Protocol

1. Reuse the pinned SU(6) source and its documented coordinate/chirality
   conventions from the [predecessor register](../su6-protection-feasibility/references.md).
   Compare only the algebraic amplitudes and internal contractions already
   admitted there; preserve the analytic mixed-mode and anomaly boundaries.
2. Reuse the [local-density source comparisons](../lagrangian-model-connections/literature-validation.md)
   and [Euler-naturality comparisons](../euler-naturality/literature-validation.md)
   only at their recorded model/action scope. Check any newly needed primary
   source location before adopting its conventions.
3. For an additional existing model or newly needed source, freeze its field
   alphabet, conjugate convention, normalization and full-relation domain.
   Any external mathematical premise remains an explicit theorem parameter.
4. If a comparison disagrees, record the mismatch or narrower statement and
   proceed to the next independent source and artificial control. Do not turn
   a source mismatch into a global halt or a paper-error claim.

No bibliography or empirical claim alone supplies a target-field equivalence.
Reconcile verified source roles into the central literature list before
integration, updating an existing entry rather than duplicating identifiers.

## Acceptance Commands For Implementation

Run focused source builds, then freshly execute persistent audits of all new
public/private/generated declarations. Allow only `propext`, `Classical.choice`
and `Quot.sound`, without relaxing existing audits. Register new sources and
audits in their proper aggregate and run `node tools/layout/check-layout.mjs`.

Serialize Math/Physics aggregate compilation as needed, then run `lake build`.
Use the resource gates in the [contract](plan.md). State artifact reuse and
warnings accurately; a full incremental build is not a fresh-source memory
audit. Include old-client and recovery checks for affected published inputs.

Run local-link, work-metadata, topic-index and diff checks. Record each
completed milestone and its assumptions in its topic; update reader-facing
usage and assumptions at verified implementation milestones. The final topic
outcome is recorded only at completion, a settled stop or verified integration.
