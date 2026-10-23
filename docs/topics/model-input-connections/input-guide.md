# Using A Selected-Field Dictionary

The existing public coefficient inputs remain valid. Use these additive
constructors when a model supplies fields inside a larger carrier or needs
one field dictionary for several coefficient/jet presentations.

## Concrete Entry Points

| Model | Entry and focused command |
| --- | --- |
| SU(6) boundary | `GUT.SU6BoundaryFieldConnection.dictionary`, `upDictionary`, `downLeptonDictionary`; `lake build GUT.SU6.Boundary.FieldConnection` |
| Lepton-parity mass radical | `Physics.LeptonParityFieldConnection.dictionary`; `lake build Physics.StandardModel.Spectrum.Representations.LeptonParityFieldConnection` |
| Complete scalar/Weyl density | `Physics.LagrangianFieldInputConnection.coefficientEquiv`, `paperCoefficientEquiv`; `lake build Physics.FieldTheory.Jets.Lagrangian.FieldInputConnection` |

Run commands from the repository root with the committed dependencies. Direct
source elaboration uses `lake env lean -j2 <source-path>.lean` after building
imports. Builds of the persistent audits also check the new declaration
inventories transitively.

## New Model

1. Supply the actual retained-group representation rho and target tau.
   For a UV source, first restrict along its retained-group homomorphism.
2. Construct the selected subrepresentation with `FieldSelection.kernel`,
   `fixed`, `boundary` or an existing mass radical. If stability follows from
   the known image maps, use `realized`.
3. Supply the actual intertwiner e, linear extraction p, membership, p(e w)=w
   and e(p s)=s on selected s. Apply `FieldSelection.ofMaps` or
   `SelectedFields.massDictionary`. Extraction equivariance is derived.
4. Specify Weyl chirality separately with `SelectedFields.withWeyl`.
   Use `internalDual` for contragredient fields, without changing chirality
   by inference.
5. Use `mixedCoefficients e f n m` for exterior/symmetric coefficient
   transport. `mixed_evaluation` preserves values on transported inputs.

`dual_pairing` handles invariant pairings through a supplied intertwiner.
`multilinear_restrict` covers independently typed species. `atVacuum` requires
a proved fixed vacuum and constructs the residual intertwiner.

## Derivatives And Interacting Equations

Represent actual carriers by bases with `FieldJetConnection.coordinates`.
`dictionaryInCoordinates` reexpresses the same proved dictionary on field
syntax; `jetsEquiv`/`fieldEquiv` lift it through all jet orders. The main
models' `derivativeDictionary` chooses bases automatically and accepts a
direction action. The convenience `coordinateJets` fixes the bosonic field
alphabet to `Unit`: one bosonic generator with trivial internal action, in
addition to its direction-dependent jets. For arbitrary bosonic field content,
supply both odd and even dictionaries to `fieldEquiv`.

Given a complete existing input P and an induced source intertwiner f,
`P.pullAlong f` uses exactly `P.relations.comap f.toLinearMap`.
`P.pullCoefficient f` preserves values and `P.imageEquiv f` identifies its
quotient image. For an equivalence e, `P.pullEquiv e` gives both coefficient
inverses. For an exact selected dictionary, use `P.selectedFields S e` and
`P.selectedCoefficientEquiv S e`.

Generate relations from the total interacting density first. Supply their
stability or use the existing density constructor that derives it. This API
does not infer the light EOM by deleting heavy variables, extend arbitrary
selected coefficients globally, or identify an unrelated density's equations.

The [dossier](../../proof/current/inputs/Physics/FIELD_CONNECTIONS.md)
states the mathematical contract; [examples and controls](literature-validation.md)
show both successful and rejected inputs.
