# Source Register

- [Input API](../../../Math/RepresentationTheory/ProhibitionInput.lean) and
  [scalar necessity](../../../Math/RepresentationTheory/ScalarProhibitionNecessity.lean).
- [Cyclic detection](../../../Math/RepresentationTheory/MixedChargeSelection.lean)
  and [standard cyclic representation](../../../Math/RepresentationTheory/CyclicCharge.lean).
- [Specifications](../../../Math/RepresentationTheory/ProhibitionSpecification.lean).
- [SM facade](../../../Physics/StandardModel/Operators/ProhibitionInputSM.lean).
- [B/L input](../../../Physics/StandardModel/Operators/ComposableBLSupport.lean).
- [Dipole selector family](../../../Physics/StandardModel/Operators/ComposableDipoleSelection.lean).
- [Koren](../koren-sm-selection/results.md), [BGW](../bgw-z6-selection/results.md)
  and [DGT/quarticity](../flavor-quarticity-controls/results.md): original model
  dictionaries, references and exact limits remain there. No new paper premise.

## New Implementation

- [Cyclic patterns](../../../Math/RepresentationTheory/ProhibitionPatterns.lean).
- [Target and joint interfaces](../../../Physics/StandardModel/Operators/ProhibitionPatterns.lean).
- [Math audit](../../../Math/RepresentationTheory/Audit/AuditProhibitionPatterns.lean)
  and [Physics audit](../../../Physics/StandardModel/Operators/Audit/AuditProhibitionPatterns.lean).
- [Restriction map](../../../Math/RepresentationTheory/GradedCompletenessRestriction.lean):
  selectedMap preserves the underlying coefficient linear map. Together with
  DGT flavor/scalar restriction identities this proves UV baryon prohibition
  from the existing IR certificate.
