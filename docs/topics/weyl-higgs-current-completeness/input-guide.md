# Combined Weyl/Higgs Input

Import `Physics.FieldTheory.Jets.WeylHiggsCompleteness` for complete
coefficients on the entire free mixed grade (2,4,1).

| Use | Entry |
| --- | --- |
| Full component input | `GUT.WeylHiggsInput.input` |
| Entire selected grade | `GUT.WeylHiggsInput.selected` |
| Union of computed Euler families | `GUT.WeylHiggsRelations.generated` |
| Global coefficient transport | `GUT.WeylHiggsRelations.coefficientEquiv` |
| Selected generated input | `GUT.WeylHiggsSelection.generatedSelected` |
| Selected coefficient transport | `GUT.WeylHiggsSelection.selectedCoefficientEquiv` |
| Current density in the selected grade | `GUT.WeylHiggsSelection.candidate` |
| Complete scalar coordinate | `GUT.WeylHiggsCompleteness.equivalence` |
| Construct a coefficient from c : ℂ | `GUT.WeylHiggsCompleteness.reconstruction c` |
| Coefficient with candidate value one | `GUT.WeylHiggsCompleteness.normalized` |
| Generated-input scalar coordinate | `GUT.WeylHiggsCompleteness.generatedEquivalence` |

`extraction` identifies the coordinate with candidate evaluation.
`reconstruct` and `extract_reconstruction` give both inverse laws.
`coefficient_dimension` is one, and `input_agreement` preserves the
coordinate under generated/component transport. Every complex scalar
constructs a unique admitted coefficient; the user supplies no rank,
moment, projection or basis-completeness proof.

For paper-specific entry points, import
`Physics.FieldTheory.Jets.WeylHiggsCompleteLiterature`.
`liCoordinate` and `murphyCoordinate` are complete native coordinates;
their extraction and inverse laws, normalized values and input transport
are checked. The DHM reversal and wrong-factor controls use the same
admitted coefficient. See the [comparison](literature-validation.md).

This input fixes one charged-lepton flavor, formal conjugate components,
global covering-SM/Lorentz symmetry and massless free equations. All
derivatives are ordinary, gauge/Yukawa couplings vanish and coefficients
are complex. Physical conjugation/Hermiticity and local gauge connections
require separate data. Existing published nonderivative/derivative inputs,
including the earlier off-shell spectator input, remain unchanged.
