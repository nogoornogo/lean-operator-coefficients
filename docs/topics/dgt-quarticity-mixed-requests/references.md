# Source Register

- [Mixed API](../../../Math/LinearAlgebra/MixedSelectionRequests.lean).
- [Existing model consumers](../../../Physics/StandardModel/Operators/MixedSelectionPatterns.lean).
- [DGT](../../../Physics/StandardModel/Operators/DgtFlavorRestriction.lean):
  all_bnv_forbidden, uv_dipoles_forbidden, ir_dipoles_allowed and actual
  restriction identities on the fixed gauge-basis dictionary.
- [Quarticity](../../../Physics/StandardModel/Operators/QuarticityAdapters.lean):
  sm_lTwo_forbidden, bare_forbidden, exists_dressed and actual action/statistics
  adapters. One selected nuR copy and complexified real eta only.
- [Original literature registers and verification](../flavor-quarticity-controls/results.md):
  pinned paper locations and model boundaries remain authoritative.
- [Representative catalogue](../prohibition-patterns/catalogue.md).

No new external paper premise. This topic repackages proved coefficient
statements into explicit requests and checks their domain/symmetry semantics.

## Implemented Consumer

- [DGT/quarticity requests](../../../Physics/StandardModel/Operators/DgtQuarticityMixedRequests.lean).
- [Strict audit](../../../Physics/StandardModel/Operators/Audit/AuditDgtQuarticityMixedRequests.lean).
- [Model dossier](../../proof/current/applications/Physics/FLAVOR_QUARTICITY_CONTROLS.md).

## Subsequent Candidate Search

The user-requested [follow-up preflight](follow-up-candidates.md) records two
new non-SUSY leads, pinned primary sources, inspected locations and estimated
adapter gaps. These are candidates only; they do not enlarge the proved topic.
