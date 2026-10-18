# Compatible Light-Action Implementation

This supersedes the design's proposed requirement that every source supply
a full-SM invariant mass on E. Keep the original design as the audit record.

## Frozen Inputs And Consumer

Core input: a continuous SM-cover x H action on the unchanged mass radical,
agreeing with its old physical-torus x H restriction. Retain the two actual
conjugations, torus unitarity, nonzero continuous compact-H target, four-weight
conditions and explicit three SM-species index conditions. Do not derive
SM invariance from torus invariance or assume common quotients/splittings.

The core consumer remains nonzero exterior qque on actual field subspaces.
No source mass SM-invariance premise is permitted in that core theorem.
Separate constructors may use preservation of the radical or invariance of
the same original mass form under a compatible action on E. Their continuity
and original residual-action agreement must be derived.

## Checkpoints

1. Compatible action interface; constructors from radical preservation and
   invariant mass; restriction, continuity and dual action compatibility.
2. Continuous SM multiplicities and compact common quotient from species
   indices; concrete SM irreducibility and field extraction.
3. Connect to the existing qque exterior theorem; controls and strict audits.

This is not a claim that the old and new sufficient conditions contain each
other. The full-SM character wrapper, new particle classifications and E6
topology remain outside these checkpoints. If an additional source premise
is needed, stop and record it rather than strengthening the statement.

## Progress

### Closed Interfaces

- [LightSMAction](../../../Physics/StandardModel/Gauge/LightSMAction.lean):
  `Compatible` specifies only an action on the unchanged radical and its
  physical-torus restriction. It contains no particle decomposition or
  tensor-existence certificate. `ofPreservesRadical` and `ofInvariantMass`
  supply this interface from the two sufficient source conditions.
- The original form and radical submodule are unchanged (`massForAction_form`,
  `massForAction_radical`). Residual restriction, dual restriction, and
  continuity are derived, including the algebraic dual with an auxiliary norm.
  `ofDecomposition` retains compatibility with the old adapter.
- [CompactMultiplicityIndex](../../../Math/RepresentationTheory/Multiplicity/CompactMultiplicityIndex.lean):
  continuous residual actions on algebraic intertwiner spaces are proved
  by injective evaluation on a finite basis. No gauge irreducibility,
  topology on the first group, or supplied multiplicity continuity is needed.
  Positive species indices give split residual quotients and a common
  nonzero irreducible quotient using compact-H character theory.
- [LightSMSpeciesIndex](../../../Physics/StandardModel/Spectrum/LightSMSpeciesIndex.lean):
  `HasTarget` specifies the three actual Hom-space indices; `common_quotient`
  combines them with the four-weight target and actual conjugations to give
  split quotients for Q/up/electron multiplicities. It assumes neither a
  full-SM invariant mass on E nor the old `Decomposition`.
- [LightSMSpeciesQque](../../../Physics/StandardModel/Operators/LightSMSpeciesQque.lean):
  `exists_model_exterior` composes the source-derived splits with the existing
  symmetric residual pairing, SM epsilon tensors and spinor/exterior proof.
  Its conclusion is `QqueSpinorExterior.HasModelExterior`, which is defined
  as existence of a nonzero SM-cover x H x SL(2,C) invariant functional on
  the fourth exterior power of the canonical Q/up-right/electron-right
  multiplicity field sum. It is not merely ordered-tensor support.

### Closed Actual-Field Endpoint

- [SmallSpecialUnitary](../../../Math/RepresentationTheory/Unitary/SmallSpecialUnitary.lean)
  proves defining SU(2)/SU(3) irreducibility using explicit determinant-one
  diagonal and basis-mixing matrices. No group classification is assumed.
- [IrreducibilityTransport](../../../Math/RepresentationTheory/Decomposition/IrreducibilityTransport.lean)
  proves enlargement-of-action and finite-dimensional dual irreducibility.
  [StandardSMIrreducibility](../../../Physics/StandardModel/Gauge/StandardSMIrreducibility.lean)
  derives the actual Q/up/electron instances, including their chiral duals.
- [EvaluationImage](../../../Math/RepresentationTheory/Multiplicity/EvaluationImage.lean)
  identifies `R tensor Hom_SM(R,K)` with the image of canonical evaluation.
  Neither K irreducibility nor surjectivity onto K is required.
  `SemisimpleSplitting.exists_retraction` derives a retraction preserving the
  original inclusion. Dualizing it gives an injection into K.dual, with a
  checked evaluation identity, and an equivalence onto its invariant image.
- [ExternalTensorDual](../../../Math/RepresentationTheory/Decomposition/ExternalTensorDual.lean)
  identifies the dual left-handed model with the right-handed gauge
  representation tensored with the dual multiplicity.
- [LightSMFieldExtraction](../../../Physics/StandardModel/Gauge/LightSMFieldExtraction.lean)
  constructs `Fields`: actual Q in K and up/electron in K.dual with the
  required SM x H equivalences. This structure is an output, not an input.
- `LightSMSpeciesQque.exists_actual_alternation` derives complete reducibility
  from compactness and continuity of the compatible action, extracts these
  fields, and transports the matched ordered coefficient with nonzero
  alternating descent. `exists_actual_exterior` gives `HasActualExterior`.

The frozen source assumptions did not change. In particular, mass invariance
under all SM on E, supplied projections, chosen common quotients and favorable
exchange symmetry are not new premises. The stronger full-SM character wrapper
is still separate. The theorem concerns the sum of participating field
subspaces, not a coefficient on all UV matter or a generated interaction.

### Verification Scope

The persistent SM-action audit includes Circle as an infinite compact residual
group, a zero mass with one-dimensional radical, and a nonzero invariant mass.
These test the action constructors, not the full species-target hypotheses.
No end-to-end new physical-model instance is claimed by those controls.

The [new field audit](../../../Physics/StandardModel/Operators/Audit/AuditActualLightFields.lean)
also embeds a one-generation Q/up/e sector into an actual direct-product
ambient representation, dualizes the projections, and transports the
nonzero alternating coefficient onto their ranges. A second control adds
singlet plus dual; its self-duality is explicitly proved. These are field
transport controls, not ambient-GUT sources satisfying both index packages.
The [mathematical audit](../../../Math/RepresentationTheory/Multiplicity/Audit/AuditEvaluationImage.lean)
also tests zero and reducible ambient spaces and the dual-evaluation identity.

Exact qque alternation regression: `python3 tools/qque/audit_one_generation.py`
passed all four tests. No contraction convention or numerical oracle was added.

- Focused build of the three new audits passed (3945 jobs including cached
  dependencies). Strict transitive checks: multiplicity index 8, light SM
  action and controls 21, species qque and its named endpoint 5. Only
  `propext`, `Classical.choice`, `Quot.sound` are allowed; no exceptions.
- `lake build` passed (5667 jobs), including the existing exterior endpoint
  audit with its 18 strict checks. Existing dependency/style warnings remain;
  the new source modules compile without warnings.
- `node tools/layout/check-layout.mjs` passed for 630 modules.
- `node tools/docs/check-links.mjs` and `git diff --check` passed.
- LSP MCP was unavailable; focused Lean builds and source reads were used.
- Initial elaboration failures were fixed without new assumptions. Directly
  expanding the source-dependent exterior tensor caused excessive type
  reduction. A generic named `HasModelExterior` endpoint and its checked
  constructor avoid that repeated expansion. Diagnostic runs used a lower
  heartbeat bound; no permanent heartbeat increase or audit relaxation was
  introduced. Temporary build logs stay outside source control.

The preceding 5667-job record belongs to intermediate commit `checkpoint 01`.
Final verification: focused build of `AuditEvaluationImage`,
`AuditActualLightFields` and `AuditLightSMSpeciesQque` passed (3957 jobs).
The two new audits passed 22 and 14 strict checks; only the standard three
axioms are allowed. `lake build` passed (5675 jobs), including the old exterior
endpoint's 18 checks. The exact qque test passed four tests; layout passed
for 638 modules. No new-file warnings, dependency changes or custom axioms.
Documentation links passed (260 Markdown files, 1458 local links, 33 heading
fragments, zero errors); `git diff --check` passed. Initial elaboration errors
were resolved by explicit carrier types, group-homomorphism extensionality and
the existing complex algebraic-closure import, without raising heartbeats.

The local condition-B connection theorem is complete. A concrete ambient
source satisfying both target packages, logical comparison with adapter A,
and the global character wrapper are separate follow-ups. No nonzero Wilson
coefficient, decay amplitude or new vacuum-dynamics result is asserted.
