# Field Correspondence, Selection And Symmetry

Supplied algebraic model data now have shared constructors connecting actual
selected fields to the existing nonderivative and derivative coefficient
inputs. The construction proves both inverse laws and selected extraction
covariance. It does not infer a particle spectrum from quantum-number labels.

## Exact Selected Fields

Let rho act on U, tau act on W, and S be a rho-stable subspace. The
[selection API](../../../../../Math/RepresentationTheory/Fields/Selection.lean)
uses mathlib's `Subrepresentation`, whose underlying submodule is S.

`FieldSelection.ofMaps S e p` accepts:

- an actual intertwiner e from W into U;
- a linear extraction p from U to W;
- membership e(w) in S, p(e(w)) = w and e(p(s)) = s for s in S.

It constructs an equivariant equivalence W ≃ S. Extraction intertwines on S
as a consequence; it is not required to intertwine on the entire ambient U.
`exact_iff` proves that an intertwiner W → S is bijective precisely when it
has a linear two-sided inverse on S. An ambient retraction is one sufficient
construction, not a chosen canonical projector.

`kernel` selects an equivariant linear kernel. `fixed` selects the common
fixed space of any family of endomorphisms commuting with the retained
action. Their mutual commutation and idempotence are unnecessary. `boundary`
adapts the existing commuting boundary-projector pair. `realized` can derive
stability itself from a concrete submodule, an equivariant inclusion and
selected reconstruction. `restrictGroup` and `reexpressEquiv` handle subgroup
restriction and changes of field coordinates.
The existing `SplitRepresentationProjection.restrictEquiv` restricts the
dictionary itself along the same homomorphism, retaining both inverse maps.

Selection is relative to the retained group. For a larger UV group, restrict
its representation first. Full UV stability is not imposed on the selected
subspace. The core requires no compactness, unitarity or semisimplicity.

## Physical Field Dictionary

The [physical constructors](../../../../../Physics/FieldTheory/Fields/SelectedFields.lean)
identify `mass B` with the radical of an invariant symmetric Weyl mass and
provide a separate equivariant Dirac-kernel constructor. `massDictionary`
uses the actual mass-zero equations and the two inverse identities.

Typed species families keep their own actual representations and
multiplicity spaces. Existing species names and input records are retained;
there is no new mandatory species format. `withWeyl rightHanded e` tensors
the internal correspondence with the specified left/right SL(2,C) action.
`internalDual e` transports the internal contragredient. These are distinct
operations. The existing Euclidean four-component adapter is not promoted
to a universal analytic charge-conjugation theorem.

The finite model instances use finite species and finite-dimensional complex
internal carriers. The shared linear results also apply without finiteness.
Formal conjugate components in local densities stay independent variables.

## Interaction And Nonderivative Coefficients

[Interaction transport](../../../../../Math/RepresentationTheory/Fields/Interactions.lean)
proves contragredient pairing invariance from an actual intertwiner, arbitrary
typed multilinear restriction, and vacuum insertion at a vector fixed by the
retained action. The fixed-vector condition belongs to vacuum insertion.

For equivariant field equivalences e and f, `mixedCoefficients e f n m`
gives an equivalence of invariant functionals on

$$
\Lambda^n U_{\rm fermion}\otimes\mathrm{Sym}^m U_{\rm boson}.
$$

It uses the existing exterior/symmetric functors and coefficient transport,
preserving the statistics quotients for every n,m. `mixed_evaluation` and
`mixed_roundtrip` prove evaluation agreement and inverse recovery.

## Derivative And Full-Relation Inputs

[Jet transport](../../../../../Math/RepresentationTheory/Fields/JetConnection.lean)
lifts equivariant constant field maps to the actual jets at every order,
using the same supplied direction representation. It then lifts them to the
exterior/polynomial mixed algebra. `fieldEquiv` constructs both inverses.
`coordinates` and `dictionaryInCoordinates` connect actual carriers to
Finsupp field syntax through chosen bases; bases are presentation choices.
`coordinateJets` is a convenience with one unchanged neutral bosonic label;
the general `fieldEquiv` accepts arbitrary odd and even field dictionaries.

The [input connection](../../../../../Math/RepresentationTheory/Fields/DerivativeConnection.lean)
accepts an existing complete input P and an intertwiner f into its source:

$$ R_{\rm new}=f^{-1}(R_{\rm full}). $$

`pullAlong` constructs this input and proves stability. `pullCoefficient`
preserves evaluations. `imageEquiv` identifies its quotient with the actual
image in P's full quotient, including for noninjective f. For a field
equivalence, `pullEquiv` gives both coefficient inverses. `selectedFields`
and `selectedCoefficientEquiv` connect an exact selected dictionary to the
existing selected-input API.

For interacting densities, generate the complete Euler/product/derivative/
IBP relations before taking this preimage. A field map by itself does not
identify the equations of a newly proposed density. No extension of arbitrary
selected coefficients to global coefficients is presumed.

## Constructed Consumers And Controls

| Consumer | Constructed connection |
| --- | --- |
| [SU(6) boundary fields](../../../../../GUT/SU6/Boundary/FieldConnection.lean) | Joint SM-gauge/residual-circle dictionaries for the left fifteen, right up component and right six components; explicit Weyl/dual conventions; invariant sterile amplitude kept separately; the old scalar-dressed wedge is recovered by fixed-vacuum insertion |
| [Lepton-parity mass kernel](../../../../../Physics/StandardModel/Spectrum/Representations/LeptonParityFieldConnection.lean) | Explicit mass inclusion/extraction, the same three-generation radical, physical species/Weyl dictionary, all-mixed-degree transport and jet syntax; previously constructed nonzero Yukawas and B1 input retained |
| [Scalar/Weyl density](../../../../../Physics/FieldTheory/Jets/Lagrangian/FieldInputConnection.lean) | Actual odd-field sign change, full generated relation preimage, coefficient evaluation/roundtrip, even-source selection and cancellation; direct paper-syntax coefficient connection |
| [Nonabelian S3 example](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/S3FieldConnection.lean) | The same kernel dictionary transports a nonzero qque coefficient and its exchange symmetry; no commutative-group or uniform-flavor premise |

The [mathematical controls](../../../../../Math/RepresentationTheory/Fields/Controls.lean)
reject a missing selected component, a noncommuting-projector product shortcut,
a wrong action map and a nonfixed vacuum; they retain a nonzero neutral
coefficient and the existing global-extension obstruction.
[Physical controls](../../../../../Physics/FieldTheory/Fields/SelectionControls.lean)
show that an extra massless dual pair can leave the dual chiral index unchanged
while preventing any exact dictionary to the smaller target. Mass mixing can
lift a proposed light space, and the known nonscalar density is rejected.

## Scope And Evidence

The named boundary construction concerns unmixed algebraic amplitudes. It
does not solve the mixed five-dimensional mode problem. The mass-kernel and
S3 examples are independent constructions, not SU(6) realizations. No anomaly,
potential-minimum, rate, RGE or empirical-spectrum theorem is added.

The [topic results](../../../../topics/model-input-connections/results.md),
[caller inventory](../../../../topics/model-input-connections/caller-inventory.md),
[source comparison](../../../../topics/model-input-connections/literature-validation.md)
and [verification](../../../../topics/model-input-connections/verification.md)
record the implementation and its exact acceptance scope.
