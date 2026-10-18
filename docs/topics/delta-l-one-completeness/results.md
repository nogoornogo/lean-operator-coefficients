# Delta L one implementation checkpoints

The bounded topic is **completed**, with master integration at `checkpoint 03`.
See [Complete residual product](#complete-residual-product) for the final
endpoint and [Master integration](#master-integration) for verification.
The earlier checkpoint notes below retain their historical open-work wording;
they do not describe current outstanding proof obligations.

## Arithmetic species reduction

[DeltaLOneSpeciesSupport](../../../Physics/StandardModel/Operators/DeltaLOneSpeciesSupport.lean)
uses counts of `q,u_R,d_R,l,e_R` and their five conjugates. Given four slots,
lepton degree one, zero hypercharge, color triality zero and even left chirality,
`admissible_iff` proves exactly the four `duql/qque/qqql/duue` count vectors.
`baryonDegree_of_admissible` and `no_conjugates` are consequences.

These are arithmetic hypotheses. Their necessity for invariant coefficients
on the full signed field sum is **not yet proved**. This checkpoint is not a
replacement for that representation-theoretic support theorem.

## Independent duql sector

[DuqlGaugeUniqueness](../../../Physics/StandardModel/Gauge/DuqlGaugeUniqueness.lean)
proves gauge uniqueness from color epsilon and weak epsilon uniqueness.
[DuqlOrderedCompleteness](../../../Physics/StandardModel/Operators/DuqlOrderedCompleteness.lean)
combines this with the two-right/two-left Weyl uniqueness theorem. Its normalized
local contraction gives a linear equivalence between ordered invariant
coefficients and

```text
Hom_R((D tensor U) tensor (Q tensor L), complex_trivial).
```

[DuqlExteriorCompleteness](../../../Physics/StandardModel/Operators/DuqlExteriorCompleteness.lean)
defines `Sector` independently inside invariant Hom from the fourth exterior
power of the four-species field sum. Its intrinsic support condition requires
one occurrence of each species. `homEquiv` supplies construction, extraction
and both inverse identities. `exists_nonzero_iff` is the corresponding exact
nonzero-existence criterion. There is no finite-dimensionality, compactness,
self-duality or matching assumption.

The group order is `(GaugeGroup × WeylSpinor.Group) × R`. Local fields are
`(gauge_carrier tensor spin_carrier) tensor multiplicity`, ordered `d,u,q,l`.
The exterior interface places all four multiplicities in a common universe;
their types need not be equal. General supplied actual-field identifications
and one-generation regression controls remain to be added.

## Reusable algebra

[DistinctSpeciesAlternation](../../../Math/RepresentationTheory/DistinctSpeciesAlternation.lean)
proves that heterogeneous multilinear maps correspond to alternating maps on
the finite field sum supported on one occurrence of each species. Restriction
and unnormalized alternatization are inverses: distinct species mean that only
the identity permutation contributes on the ordered probe. The equivariant
version descends to independent exterior Hom.

[FourTensorMultilinear](../../../Math/RepresentationTheory/FourTensorMultilinear.lean)
connects heterogeneous four-linear maps to the balanced binary tensor product,
including the invariant Hom equivalence. These helpers do not assert anything
about repeated-species exchange constraints.

## Four equal doublets and same-chirality spinors

[FourDoubletInvariant](../../../Math/RepresentationTheory/Unitary/FourDoubletInvariant.lean)
proves a two-coordinate linear equivalence for four defining SU(2) doublets.
The inverse is the sum of the `12|34` and `13|24` epsilon products. Diagonal
phases remove unbalanced coordinates; a signed flip relates complementary
coordinates; one plane rotation gives the remaining relation. The two probes
are `0101` and `0011`. No generated elimination table is used.

[FourSameWeylCompleteness](../../../Physics/FieldTheory/Spinor/FourSameWeylCompleteness.lean)
transports this exhaustiveness to four left or four right Weyl spinors.
The restriction for right spinors uses conjugated group elements and proves
the double-conjugation identity; it does not identify conjugation with a
complex-linear map. `coordinates` is a linear equivalence with `complex × complex`
for each chirality. These are local coefficients before repeated-species flavor
exchange conditions. The duue descent is established below; qqql remains open.

## Independent duue sector

[FiniteInvariantFactor](../../../Math/RepresentationTheory/FiniteInvariantFactor.lean)
extracts any exhaustive finite local invariant basis by dual probes, without
finite-dimensionality of the residual representation.
[DuueGaugeUniqueness](../../../Physics/StandardModel/Gauge/DuueGaugeUniqueness.lean)
proves that the gauge contraction is the color epsilon times the electron scalar.
[DuueOrderedCompleteness](../../../Physics/StandardModel/Operators/DuueOrderedCompleteness.lean)
combines this with the two right-Weyl contractions and extracts two residual maps
on `(U tensor U) tensor (D tensor E)`. The slot order is `u,u,d,e`.

[DuueExchange](../../../Physics/StandardModel/Operators/DuueExchange.lean)
proves that full first-two-slot antisymmetry is equivalent to the following
explicit equations, with `S` exchanging the two up multiplicities:

```text
k1(S t) = k1(t)
k0(S t) + k1(t) = -k0(t).
```

`exteriorEquiv` classifies the independently defined degree-(2,1,1) exterior
sector by this residual subspace, with construction, extraction and both
inverse identities. `exists_nonzero_iff` gives the exact nonzero-existence
criterion. No SM or Lorentz invariance remains in the residual conditions.
[FourSlotCoefficientEquiv](../../../Math/RepresentationTheory/FourSlotCoefficientEquiv.lean)
supplies the reusable exterior descent; its inverse includes the required
factor of one half for the repeated species.

[DuueResidualCompleteness](../../../Physics/StandardModel/Operators/DuueResidualCompleteness.lean)
solves these equations: `k0` is unrestricted and `k1 = -k0 - k0 ∘ S`.
`homEquiv` therefore identifies the exterior sector with the single space
`Hom_R((U tensor U) tensor (D tensor E), complex_trivial)`.
In particular, imposing symmetric up multiplicities would incorrectly shrink
the general input space. `onFieldsEquiv` transports the independent exterior
sector through supplied equivariant actual-field identifications.

[DuueScalarFlavor](../../../Physics/StandardModel/Operators/DuueScalarFlavor.lean)
proves the one-dimensional multiplicity criterion
`exists_nonzero_iff_charge_trivial`: a nonzero exterior coefficient exists iff
`(u r 1)^2 * d r 1 * e r 1 = 1` for every residual group element `r`.
For three trivial scalar multiplicities, `oneGenerationEquiv` is a linear
equivalence with the complex numbers and `oneGeneration_finrank` proves
dimension one. This is a coefficient-space result, not a generated coupling.

These results do not yet embed the sector into the full signed-species Delta L
one classification. Actual-field transport and regressions for the remaining
families are still open.

## Qqql local factors, exchanges and exterior foundations

[FourWeakWeylCompleteness](../../../Physics/StandardModel/Operators/FourWeakWeylCompleteness.lean)
classifies the independent weak/Lorentz local invariant space by four product
contractions with four dual probes. `FiniteInvariantFactor.product_formula`
supplies the general finite-product exhaustiveness argument.
[QqqlLocalCompleteness](../../../Physics/StandardModel/Operators/QqqlLocalCompleteness.lean)
adds the unique color epsilon factor and extracts four residual Hom coordinates.
Its input is explicitly regrouped under `SU(3) × (SU(2) × Spin)` (and the
independent residual group). It does **not** yet identify the physical SM-field
tensor with that input or account for its hypercharge via a proved transport.

[FourDoubletProductExchange](../../../Math/RepresentationTheory/Unitary/FourDoubletProductExchange.lean)
proves both adjacent-exchange formulas, their involutions and the braid relation.
[QqqlExchange](../../../Physics/StandardModel/Operators/QqqlExchange.lean)
defines an explicit residual subspace and proves that these equations are
necessary and sufficient for adjacent full-quark antisymmetry of the specified
color/weak/Weyl contractions. It does not assume arbitrary invariant
coefficients are already in that contraction image.

For pattern `(A,A,A,B)`,
[FourSlotTripleSector](../../../Math/RepresentationTheory/FourSlotTripleSector.lean)
independently defines the invariant exterior sector by vanishing on pure-species
tuples outside degree `(3,1)` and proves ordered-slot extensionality.
[FourSlotTripleAlternation](../../../Math/RepresentationTheory/FourSlotTripleAlternation.lean)
establishes the factor-six normalization.
[FourSlotTripleRestriction](../../../Math/RepresentationTheory/FourSlotTripleRestriction.lean)
provides restriction, reconstruction and a linear equivalence with ordered
coefficients alternating under every permutation fixing the last slot.
The inverse uses `1/6` times alternatization; neither finite-dimensionality
nor a contraction-image assumption is required.

### Physical qqql completeness

[QqqlGaugeRegroup](../../../Physics/StandardModel/Gauge/QqqlGaugeRegroup.lean)
proves the physical gauge-field regrouping and hypercharge cancellation on the
group action. [QqqlOrderedCompleteness](../../../Physics/StandardModel/Operators/QqqlOrderedCompleteness.lean)
transports through the surjective projection dropping the neutral hypercharge
factor and extracts all four local coordinates, with an explicit contraction inverse.

[FourSlotTripleExchange](../../../Math/RepresentationTheory/FourSlotTripleExchange.lean)
proves that the two adjacent exchanges are equivalent to every first-three-slot
permutation. [QqqlExteriorCompleteness](../../../Physics/StandardModel/Operators/QqqlExteriorCompleteness.lean)
composes these results with the independent exterior-sector inverse:

```text
QqqlExteriorCompleteness.Sector q l ≃ₗ[ℂ] QqqlExchange.residualSpace q l.
```

Both inverses and the nonzero iff are proved. There are no remaining local
gauge/Weyl hypotheses on the right-hand side, and no finite-dimensional flavor
assumptions. The right-hand side is an explicit finite exchange kernel, not
four freely selectable coefficients.

[FourSlotTripleTransport](../../../Math/RepresentationTheory/FourSlotTripleTransport.lean)
preserves the independently defined degree sector under supplied species-wise
equivariant field identifications; `onFieldsEquiv` exposes this adapter.
[QqqlScalarFlavor](../../../Physics/StandardModel/Operators/QqqlScalarFlavor.lean)
proves that neutral scalar multiplicities give one coefficient and finrank one.
Its four coordinates have the pattern `[[2z,-z],[-z,2z]]`.
More generally its scalar equivalence retains the residual neutrality hypothesis
`(q r 1)^2 * q r 1 * l r 1 = 1` explicitly.

This checkpoint completed the individual qqql family. The full signed-field
support and total classification were established subsequently below.

## Signed-species exclusion foundations

`DeltaLOneSpeciesSupport.gauge_admissible_iff` separates the gauge arithmetic
from Lorentz invariance: slot count four, lepton degree one, zero hypercharge
and color triality leave exactly six count patterns. Besides the four expected
families, these are `antiQddL` (one conjugate q, two conjugate d, one l) and
`antiDddE` (three conjugate d, one e). Both have three left Weyl slots.

[OddWeylInvariant](../../../Physics/FieldTheory/Spinor/OddWeylInvariant.lean)
proves that three Weyl slots of one chirality and one of the other admit no
invariant scalar, for either chirality choice. This uses an explicit nonunitary
SL(2,C) diagonal action and sixteen basis coordinates, not an SU(2)-only argument.
`external_eq_zero` retains the conclusion with arbitrary independent
gauge/flavor spectators, without a finite-dimensionality assumption.

The [signed-field extension](signed-fields.md) now derives hypercharge/triality
from the standard actions, excludes both extra candidates in every species
ordering, and proves the four-family support theorem. The independent full-sector
species split and both inverse identities are also proved. The factors are now
identified with the individual classifications as described below.

## Complete residual product

[DeltaLOneFamilyCompleteness](../../../Physics/StandardModel/Operators/DeltaLOneFamilyCompleteness.lean)
connects each intrinsic family summand to the existing ordered classification.
The new reusable
[SpeciesPatternAssembly](../../../Math/RepresentationTheory/SpeciesPatternAssembly.lean)
proves normalized extension, support, restriction, and both inverses. Only
permutations preserving the pattern contribute to its canonical restriction.
Their cardinalities are kernel-checked as `1,2,6,2` for `duql,qque,qqql,duue`.
This avoids assuming that four physical tensor Hom spaces are already classified.

[DeltaLOneCoefficientCompleteness](../../../Physics/StandardModel/Operators/DeltaLOneCoefficientCompleteness.lean)
provides the final linear equivalence on the independent full signed-field input:

```text
DeltaLOneSignedFields.Sector flavor 1 ≃ₗ[ℂ]
  ResidualDuql × (SymmetricResidualQque × (ExchangeResidualQqql × ResidualDuue)).
```

The residual factors, in fixed order, are:

- `DuqlOrderedCompleteness.Residual (flavor 2) (flavor 1) (flavor 0) (flavor 3)`:
  invariant residual functionals on `(D ⊗ U) ⊗ (Q ⊗ L)`.
- `QquePhysicalExteriorCompleteness.residualSpace (flavor 0) (flavor 1) (flavor 4)`:
  residual functionals on `(Q ⊗ Q) ⊗ (U ⊗ E)` symmetric in the quark flavors.
- `QqqlExchange.residualSpace (flavor 0) (flavor 3)`:
  four residual functionals on `(Q ⊗ Q) ⊗ (Q ⊗ L)` subject to the proved
  two adjacent exchange equations, not four independent coordinates.
- `DuueOrderedCompleteness.Residual (flavor 1) (flavor 2) (flavor 4)`:
  unrestricted residual functionals on `(U ⊗ U) ⊗ (D ⊗ E)` after solving
  repeated-up exchange; no symmetric-up hypothesis is imposed.

There are no remaining SM/Lorentz conditions or finite-dimensionality
assumptions. `extract` and `reconstruct` expose the forward and inverse maps;
`reconstruct_extract` and `extract_reconstruct` check both inverses.
`extract_injective`, `reconstruct_surjective`, `coefficient_ext`, and
`nonzero_iff` give uniqueness, construction of every allowed coordinate tuple,
and existence iff some residual factor is nonzero.
Reconstruction is the sum of the four normalized, alternating, supported
family reconstructions. The legacy qque normalization boundary above is unchanged.

[DeltaLOneInputTransport](../../../Physics/StandardModel/Operators/DeltaLOneInputTransport.lean)
proves lepton-degree transport through species-wise equivariant identifications;
`onFieldsEquiv` classifies the independent sector on supplied actual fields.
It does not discover such identifications from charges or a UV label.
`negativeEquiv` classifies degree `-1` semilinearly under the explicit conjugation
involution/species-reversal interface. No involution is asserted for arbitrary
unrelated negative multiplicities.

[DeltaLOneRegression](../../../Physics/StandardModel/Operators/DeltaLOneRegression.lean)
proves:

- `oneGenerationEquiv` and `oneGeneration_finrank`: trivial residual actions
  on scalar multiplicities give exactly four total coefficients.
- `zero_quark_factors`: a zero quark multiplicity kills precisely the three
  factors containing quarks; duue is not incorrectly discarded.
- `zero_quark_up`: if quark and up multiplicities are both zero, the total sector is zero.
- `scalar_charge_vanish`: if each of the four product characters is nontrivial,
  the entire scalar-flavor sector is zero. Scalar multiplicity is not neutrality.

This is coefficient completeness in the accepted dimension-six,
derivative-free SM four-fermion scope. It does not determine a generated Wilson
coefficient, UV matching, matrix elements, or decay rates.

## Verification

The strict transitive audit is
[AuditDeltaLOneFoundations](../../../Physics/StandardModel/Operators/Audit/AuditDeltaLOneFoundations.lean).
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

- `lake build Physics.StandardModel.Operators.Audit.AuditDeltaLOneFoundations`:
  passed, 131 strict transitive axiom checks (3290 jobs), including total residual
  completeness, both inverses, actual-field transport, regression controls,
  and conditional semilinear residual conjugation.
- `lake build`: passed (6030 jobs).
- `node tools/layout/check-layout.mjs`: passed (977 modules).
- `node tools/docs/check-links.mjs`: passed (347 Markdown files, 2168 local inline
  links, 33 heading fragments, zero errors).
- `git diff --check`: passed.

No warnings were emitted by the new modules. The full build replayed existing
deprecation and style/linter warnings in unchanged modules; these are outside
this topic's changes and are not new theorem claims. No `sorry`, custom axioms, audit exceptions
or dependency changes were introduced.

### Master integration

The verified topic endpoint is `checkpoint 01`. Following explicit user authorization,
`git merge --no-ff proof/delta-l-one-completeness` integrated it into `master`
at `checkpoint 02` without conflicts. The target
had not advanced beyond the recorded base commit.

On the merged state, the strict audit passed again (131 checks, 3290 jobs),
`lake build` passed again (6030 jobs), layout checks passed (977 modules), local
links passed (347 Markdown files, 2168 links, 33 fragments), and `git diff --check`
passed. The existing replayed deprecation/linter warnings remain unchanged.
The subsequent integration-record edits are documentation-only: link and diff
checks were repeated, and no Lean build was rerun after those edits. The topic
branch is retained and no remote push was made.

## Remaining boundaries and integration

- No proof obligation remains within the accepted bounded endpoint.
- Actual-field identifications and conjugation involution remain model inputs;
  they are not universally inferred from arbitrary multiplicity representations.
- Cross-topic input-interface unification was outside this topic and was later
  completed in the [common interface topic](../operator-completeness-interface/integration.md).
  Extra species and arbitrary dimension classification remain outside this endpoint.
- User-authorized integration into `master` is complete; no remote push has been made.
