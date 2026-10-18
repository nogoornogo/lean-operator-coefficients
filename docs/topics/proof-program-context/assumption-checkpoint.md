# Assumption checkpoint

Scoped input and relaxation catalogue. These are individual result hypotheses,
not the current general theorem's universal input package. Use the
[current assumptions](../../proof/ASSUMPTIONS.md) for maintained entries.

## Layered Ledgers

- [Math](../../proof/current/inputs/Math/ASSUMPTIONS.md): algebraic hypotheses, geometric classification and external mathematical inputs.
- [Physics](../../proof/current/inputs/Physics/ASSUMPTIONS.md): fields, masses, operator sectors and physical scope.
- [GUT](../../proof/current/inputs/GUT/ASSUMPTIONS.md): specified groups, embeddings, matter, vacua and model adapters.

Classify each premise by its own nature, not by its eventual consumer. Explain it once in its owning ledger and link across layers. A derived property is not an additional input; a checked conditional theorem does not establish its external premise. The E6 topology premise is [mathematical](../../proof/current/inputs/Math/assumptions/concrete-model-inputs.md#e6-literature-boundary), whereas the candidate matter and selection-rule application are [model-specific](../../proof/current/inputs/GUT/assumptions/concrete-model-inputs.md#model-specific-adapters).

The input/derived/external/excluded distinctions are stated at each endpoint. No split changes a theorem hypothesis or verification baseline. Recorded Lean results have not been rebuilt for this documentation change.

## Current Endpoints

| Endpoint | Residual group H | Required inputs / nonzero target | Checked conclusion |
| --- | --- | --- | --- |
| Intrinsic qque coefficient classification | Any abstract group | None; supplied multiplicity actions and, for actual-field transport, SM x H field identifications | Linear equivalence of the independent degree-(2,1,1) invariant exterior sector with Hom_H(Sym^2 V_Q, V_uc tensor V_ec); nonzero Hom is necessary and sufficient |
| [Dimension-six Delta L = 1](../delta-l-one-completeness/results.md) | Any abstract group | Arbitrary signed-species multiplicity actions; equivariant identifications for actual-field transport | Independent lepton-degree +1 exterior sector is equivalent to the four-family residual-Hom product; negative-sign correspondence additionally needs a field involution |
| [Specified Delta B = 2](../delta-b-two-model-interface/flavor-hom.md) | Any abstract group | Finite-dimensional up/down multiplicities and actual-field identifications | Degree-(2,4) six-right-quark exterior sector is equivalent to the typed-exchange residual Hom; trivial scalar specialization has dimension 2 |
| [Weinberg Delta L = 2](../delta-l-two-weinberg/results.md) | Any abstract group | Lepton multiplicity, one residual-trivial Higgs doublet, and supplied field identifications | LLHH sector is equivalent to Hom_H(Sym^2 F,C); nonzero supplied neutral VEV identifies it with Majorana forms |
| [CLFV dipole channels](../clfv-dipole-completeness/integration.md) | Supplied residual group | Prescribed chiral B/W fields, residual-trivial Higgs and model matching/domain inputs | Complete residual-Hom coordinates and generation criteria on the specified admissible domain |
| Full light-species classification | Any abstract group | No positivity; finite-dimensional SM-cover x H representation with semisimple SM restriction | Field identifications from full multiplicities, and necessary/sufficient nonzero and zero qque criteria; continuous compatible SM action suffices on the mass radical |
| Common irreducible criterion | Any group with semisimple Sym^2 Q; compact continuous Q suffices | No positivity; actual multiplicity representations | Full qque nonzero iff Sym^2 Q and up-left tensor electron-left share a simple constituent; full-radical compact adapter included |
| Abelian qque only | Arbitrary Abelian group | Q | Neutral qque signature with actual field-slot support and four nonzero radical eigenvectors |
| Abelian pair | Arbitrary Abelian group | Q and down, independently | Neutral qque/duql signatures with legacy full support and all fifteen actual radical eigenvectors |
| Non-Abelian qque only | Arbitrary finite group, not necessarily Abelian | Q representation | Nonzero H-equivariant linear functional on the ordered actual qque light tensor product |
| Compact continuous qque | Compact topological group, not necessarily finite or Abelian | Continuous nonzero finite-dimensional Q representation | The same nonzero H-equivariant functional on the actual qque light tensor product |
| Route A: explicit SM x H qque adapter | Compact H for source extraction; arbitrary H for tensor assembly | Continuous nonzero Q target; additionally supplied compatible full-SM field decompositions | Nonzero ordered SM x H invariant functional on the supplied actual Q/up-right/electron-right subrepresentations |
| Route A: spinor/exterior extension | Same compact source and full-SM decomposition | Same Q target; no extra generation or coefficient premise | Nonzero qque-derived invariant functional on the fourth exterior power of the actual participating light fields with left/right spinors, under SM-cover x H x SL(2,C) |
| Route B: species-index exterior connection | Compact continuous H; compatible continuous SM-cover x H action on the original radical | Continuous nonzero finite-dimensional Q target; four-weight and three SM-species index equations | Actual participating field subspaces and their identifications are derived; their qque alternating descent is nonzero |
| Signed virtual-index exterior connection | Compact continuous H; the same compatible action on the radical | Normalized finite continuous irreducible virtual targets, positive Q total dimension, matching species/weight indices | A common positive constituent, actual fields and nonzero qque alternating/exterior descent are derived; other coefficients may be negative |
| Shared-positive-constituent connection | Compact continuous H; continuous compatible SM-cover x H action on the radical | Three normalized virtual species-index equations and one common strictly positive coefficient position | Actual qque alternating/exterior descent; no whole-index equality, positive total dimension, four-weight or conjugation premise |
| Pairwise-positive-constituent connection | The same compact H and compatible continuous action | Three normalized virtual species-index equations; positive support shared by Q/up and Q/e separately | The same nonzero actual qque alternating/exterior conclusion; the two constituents may differ |
| Automatic species-index connection | The same compact H and compatible continuous action | Pairwise positive support of the constructed actual species indices | The normalized family, signed coefficients and species matching are derived, then the same actual exterior conclusion follows |
| Exact-spectrum entry to route B | Same compact H and compatible continuous action on K | Exact SM-only spectrum n > 0 generations plus s singlets; no supplied H target | Both target packages are derived, followed by the actual nonzero alternating/exterior qque coefficient |
| Balanced species extension | Compact H; compatible continuous action on the new radical | Exact-SM reference with two conjugations and T-unitarity; H-equivariant balanced Q/up/e multiplicity decompositions | Species indices and positive support are derived, then actual nonzero qque alternating/exterior descent |
| Global vectorlike spectrum | Compact H; compatible continuous action on the new radical | Same exact-SM reference; finite continuous SM-cover x H representation X and equivalence K = K0 + X + X.dual | All balanced multiplicity decompositions, positive support and actual nonzero qque exterior descent are derived |
| Non-Abelian pair | Arbitrary finite group, not necessarily Abelian | Q and down representations, independently | Such nonzero functionals for both qque and duql at torus-neutral slots |

The pair source theorems are [TwoConjugationQque](../../../Physics/StandardModel/Spectrum/TwoConjugationQque.lean)
and [TwoConjugationLightQque](../../../Physics/StandardModel/Operators/TwoConjugationLightQque.lean).
Their fifteen-weight targets remain sufficient. The newer qque-only endpoints
in [FourWeightQque](../../../Physics/StandardModel/Spectrum/FourWeightQque.lean) and
[FourWeightLightQque](../../../Physics/StandardModel/Operators/FourWeightLightQque.lean)
need matching only at 0, 3, 8, 14. Both retain two actual conjugations and the
opposite-weight dual terms. None asserts a nonzero decay amplitude.
The [compact continuous endpoint](../../proof/current/applications/Physics/COMPACT_LIGHT_QQUE.md) adds residual-action
continuity and removes the finiteness requirement for qque.

Routes A and B reach full-SM/spinor/exterior conclusions under different
additional inputs, detailed below. No inclusion between their complete input
packages is proved. In this ledger `SM-cover` means
`S = SU(3) x SU(2) x U(1)`, with the repository's integral `6Y` convention;
full-SM invariance refers to this covering-group action.

The current endpoints also include the [common completeness interface](assumption-checkpoint.md#common-completeness-interface),
the [specified VEV and flavor stabilizers](assumption-checkpoint.md#specified-vev-and-flavor-stabilizers),
and [Takagi existence with full unitary Majorana classification](assumption-checkpoint.md#full-unitary-majorana-stabilizers-and-takagi-existence).
Their hypotheses are recorded separately below: shared transport is not an
all-operator completeness theorem, and a specified mass stabilizer is not
automatically the full interacting symmetry.

## Invariant Mass Extension Protection

See the [Math ledger](../../proof/current/inputs/Math/ASSUMPTIONS.md#invariant-mass-extension-protection).

## UV-Generated Yukawa Protection And Exact Radicals

See the [Physics ledger](../../proof/current/inputs/Physics/assumptions/mass-protection.md#uv-generated-yukawa-protection-and-exact-radicals).

## Generated Matching Certificate

See the [Physics ledger](../../proof/current/inputs/Physics/assumptions/concrete-model-inputs.md#generated-matching-certificate).

## Yukawa Classification And Specified Spectra

See the [Math ledger](../../proof/current/inputs/Math/ASSUMPTIONS.md#yukawa-classification-and-specified-spectra).

## Structural Inputs For Conjugation Routes

See the [Physics ledger](../../proof/current/inputs/Physics/assumptions/conjugation.md#structural-inputs-for-conjugation-routes).

## Endpoint-Specific Inputs

See the [Physics ledger](../../proof/current/inputs/Physics/assumptions/source-routes.md#endpoint-specific-inputs).

## Coefficient Classification

See the [Physics ledger](../../proof/current/inputs/Physics/assumptions/coefficient-classification.md#coefficient-classification).

## Additional Bounded Operator Classifications

See the [Physics ledger](../../proof/current/inputs/Physics/assumptions/bounded-sectors.md#additional-bounded-operator-classifications).

## Common Completeness Interface

See the [Math ledger](../../proof/current/inputs/Math/ASSUMPTIONS.md#common-completeness-interface).

## Specified VEV And Flavor Stabilizers

See the [GUT ledger](../../proof/current/inputs/GUT/ASSUMPTIONS.md#specified-vev-and-flavor-stabilizers).

## Full Unitary Majorana Stabilizers And Takagi Existence

See the [Math ledger](../../proof/current/inputs/Math/ASSUMPTIONS.md#full-unitary-majorana-stabilizers-and-takagi-existence).

## Derived Properties, Not Extra Assumptions

See the [Physics ledger](../../proof/current/inputs/Physics/assumptions/derived-properties.md#derived-properties-not-extra-assumptions).

## What The Conclusions Do And Do Not Say

See the [Physics ledger](../../proof/current/inputs/Physics/assumptions/conclusion-meaning.md#what-the-conclusions-do-and-do-not-say).

## Conditions No Longer Required

See the [Physics ledger](../../proof/current/inputs/Physics/assumptions/concrete-model-inputs.md#conditions-no-longer-required).

## Model-Specific Adapters

See the [GUT ledger](../../proof/current/inputs/GUT/assumptions/concrete-model-inputs.md#model-specific-adapters).

## Physical Interpretation And Exclusions

See the [Physics ledger](../../proof/current/inputs/Physics/assumptions/physical-scope.md#physical-interpretation-and-exclusions).

The SU(6) examples formerly beside the general Yukawa classification are now under [specified SU(6) Yukawa spectra](../../proof/current/inputs/GUT/assumptions/concrete-model-inputs.md#specified-su6-yukawa-spectra). General flavor inputs are under [flavor stabilizer inputs](../../proof/current/inputs/Physics/assumptions/flavor-stabilizers.md#flavor-stabilizer-inputs).
