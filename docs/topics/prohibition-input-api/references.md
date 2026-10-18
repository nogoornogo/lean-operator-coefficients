# Source and Interface Register

These repository sources define the intended semantics. They are proof inputs
and reusable interfaces, not assumptions that a physical UV model realizes
the admitted fields. Inspect declarations before implementation; proposed API
names in the plan are not existing declarations.

- [SelectionCriteria](../../../Math/LinearAlgebra/SelectionCriteria.lean):
  existing Allowed/Forbidden zero/nonzero semantics; reuse these.
- [ProhibitionSpecification](../../../Math/RepresentationTheory/ProhibitionSpecification.lean):
  stable arbitrary targets, union/indexed union and content satisfaction.
- [ComposableProtection](../../../Math/RepresentationTheory/ComposableProtection.lean):
  forbidden_iff, protected_iff and charge sufficiency consumers.
- [GradedMixedCompleteness](../../../Math/RepresentationTheory/GradedMixedCompleteness.lean):
  independently constructed selected input/factor equivalence at arbitrary degrees.
- [TypedMixedSeparatedHom](../../../Math/RepresentationTheory/TypedMixedSeparatedHom.lean):
  actual residual carrier after local and exchange relations.
- [CommonIrreducible](../../../Math/RepresentationTheory/Decomposition/CommonIrreducible.lean):
  nonzero_iff/all_zero_iff with explicit source semisimplicity.
- [InvariantFunctionalCoordinates](../../../Math/RepresentationTheory/InvariantFunctionalCoordinates.lean):
  actual invariant-functional coordinates and unrestricted/trivial action equivalences.
- [GradedSymmetryProtection](../../../Math/RepresentationTheory/GradedSymmetryProtection.lean)
  and [restriction](../../../Math/RepresentationTheory/GradedCompletenessRestriction.lean):
  preservation versus surjectivity and genuine restriction maps.
- [ComposableBLSupport](../../../Physics/StandardModel/Operators/ComposableBLSupport.lean):
  reusable signed SM/Higgs admission and replaceable B/L targets.
- [WeinbergScalarFlavor](../../../Physics/StandardModel/Operators/WeinbergScalarFlavor.lean)
  and [SM interface](../../../Physics/StandardModel/Operators/WeinbergSMInterface.lean):
  certified actual LLHH coefficient space and existing nonzero controls.
- [Earlier bounded residual criteria](../residual-selection-criteria/README.md):
  avoid duplicating predicates or overstating one-generation cyclic converses.
- [Completed model controls](../flavor-quarticity-controls/results.md),
  [Koren](../koren-sm-selection/results.md), [BGW](../bgw-z6-selection/results.md):
  regression candidates, with field-domain and source boundaries preserved.

The external papers supporting those model dictionaries remain pinned in their
own source registers. This plan adds no new external theorem premise and makes
no literature-wide claim. New source use during implementation must be recorded
here or in the owning result's register.

## Implemented Sources

- [ProhibitionInput](../../../Math/RepresentationTheory/ProhibitionInput.lean)
  and [scalar necessity](../../../Math/RepresentationTheory/ScalarProhibitionNecessity.lean).
- [SM consumer](../../../Physics/StandardModel/Operators/ProhibitionInputSM.lean).
- [Math audit](../../../Math/RepresentationTheory/Audit/AuditProhibitionInput.lean)
  and [Physics audit](../../../Physics/StandardModel/Operators/Audit/AuditProhibitionInputSM.lean).
- mathlib `Mathlib/LinearAlgebra/Dual/Lemmas.lean`, at the unchanged pinned
  dependency: `Module.Projective.exists_dual_ne_zero` constructs a functional
  detecting a nonzero vector. Projectivity is supplied by the vector-space
  instance; no finite basis assumption or external theorem premise is added.
- [Input dossier](../../proof/current/inputs/Math/PROHIBITION_INPUT.md).
