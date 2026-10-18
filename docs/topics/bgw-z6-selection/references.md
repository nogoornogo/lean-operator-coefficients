# Source Register

- Babu, Gogoladze, Wang, *Gauged Baryon Parity and Nucleon Stability*:
  [hep-ph/0306003v1](https://arxiv.org/abs/hep-ph/0306003v1),
  [PDF](https://arxiv.org/pdf/hep-ph/0306003v1),
  [publication](https://doi.org/10.1016/j.physletb.2003.07.036).
  Sec. 2, Tables 1–2 and Eq. (4) are the target; right-handed-neutrino and
  UV/anomaly conclusions are excluded. The implemented signed dictionary must
  translate right-handed u/e/d fields to opposite charges of printed uc/ec/dc.
- [Candidate preflight](../composable-prohibition-specifications/literature-candidates.md).
- [Composable input interface](../composable-prohibition-specifications/interfaces.md).
- [BnvMixedInput](../../../Physics/StandardModel/Operators/BnvMixedInput.lean):
  `hypercharge_of_nonzero`, `value_ext` on actual typed field actions.
- [CyclicCharge](../../../Math/RepresentationTheory/CyclicCharge.lean): scalar
  cyclic representations and faithful-character neutrality.

The second and third preflight candidates are excluded from direct verification
because their supersymmetric model dictionaries are outside this study.

## Verified Repository Output

- [Source](../../../Physics/StandardModel/Operators/BgwZ6Selection.lean):
  printed dictionary, conjugates, cleared integral identity, actual copy/field
  actions, faithful neutrality, baryon divisibility and composed all-degree zero.
- [Persistent audit](../../../Physics/StandardModel/Operators/Audit/AuditBgwZ6Selection.lean).
- [Existing Weinberg interface](../../../Physics/StandardModel/Operators/WeinbergSMInterface.lean):
  `Inputs.higgsEquiv` requires the trivial-residual Higgs representation;
  [graded comparison](../../../Physics/StandardModel/Operators/GradedWeinbergComparison.lean)
  `scalarFlavor` is trivial. This mismatch prevents direct reuse as a
  charged-Higgs nonzero certificate, without claiming the desired theorem false.

## Charged-Higgs Follow-Up Sources

- [Actual charged-field adapter](../../../Physics/StandardModel/Operators/BgwChargedHiggsWeinberg.lean):
  whole LLHH phase cancellation, neutral-copy field identifications,
  coefficient equivalence and nonzero witness.
- Existing `WeinbergSMInterface.oneGenerationEquiv` supplies the already
  proved neutral-copy coefficient space. `InvariantCoefficientTransport.alongEquiv`
  transports it through the independently proved domain action equivalence.
  This resolves the earlier direct-use mismatch without assuming a Higgs-only
  charged-to-neutral representation equivalence. No new literature premise.
