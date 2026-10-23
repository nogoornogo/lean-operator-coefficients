# Choosing An Input Route

For new derivative-side work use `Math.DerivativeInterface`. It provides
purpose-specific factories and shared operations. Published nonderivative
callers keep their existing imports, types, maps and proof obligations.
The model-specific entries below extend the constructions of the same
`Input`; they use its existing coefficient and quotient operations.

## Choose The Input Data

| Purpose | Factory | Caller supplies |
| --- | --- | --- |
| Mixed Bose/Fermi source with IBP, including degree zero | `Math.DerivativeInterface.graded rhoF rhoB sigma n m d` | Field and direction representations, odd/even field counts and natural-number derivative degree |
| Full commutative EOM/IBP source | `Math.DerivativeInterface.equations D R rho stable` | Derivatives, seed set, source representation and combined-relation stability |
| Existing actual Lorentz scalar model | `GUT.ScalarDerivativeInterface.scalar lambda` | Coupling only; the actual source and Lorentz stability are already proved |
| Gaugeless Higgs with global SM/Lorentz symmetry | `GUT.HiggsStandardInput.input a b` | Two complex potential parameters; generated equations and actual symmetry stability are packaged |
| Paired free Weyl equations with Higgs spectators | `GUT.PairedWeylInput.generated` | No parameters for the fixed kinetic model; both Weyl equations and actual Lorentz stability are packaged |
| Other supplied stable relations, including mixed EOM/IBP | `Math.DerivativeInterface.Input` | Source action, complete linear relation submodule and its stability |

For the Higgs entry import `Physics.FieldTheory.Jets.HiggsStandardInput`.
It uses ordinary derivatives and the gaugeless, Yukawa-free density; the
internal symmetry is global. For the paired Weyl entry import
`Physics.FieldTheory.Jets.PairedWeylGeneratedInput`. Its even Higgs labels
are off-shell spectators: this entry imposes both Weyl equations, with
Lorentz symmetry, but supplies no Higgs EOM or mixed weak/hypercharge action.
The [generated-input guide](../derivative-literature-foundations/input-guide.md)
gives the density conventions, direct-input alternatives and proved inverse
coefficient maps. Each represented model entry includes the relevant action
and stability proofs; callers reuse them for the supported model.

The graded factory constructs the actual source/action, IBP range and stability.
At d=0 the IBP range is bottom; at d+1 it is the actual divergence range from
degree d. Directions may mix. To import an already constructed original mixed
coefficient, `DerivativeInterface.fromNonDerivative` supplies the inverse
zero-jet correspondence, with the original evaluation preserved. No migration
of existing nonderivative callers is required.

The [nonderivative input checks](../derivative-literature-foundations/nonderivative-recheck.md)
consume original coefficients through this route, including explicit Bose,
Fermi, mixed and vacuum examples. Both round trips, evaluation, nonzero and
forbidden conditions are checked, with arbitrary direction actions. A
separate complete scalar example checks the published finite-local route
with no added relation. These examples are compiled Lean usages, not only
type-level descriptions.

The equations factory retains the complete EOM differential ideal and actual
divergence range on the whole source. It assumes no homogeneous decomposition.
This factory requires a commutative complex algebra. For direct mixed EOM,
construct `Input` with `Math.TwoSidedDifferential.combined D R` as its relation
module, and supply the source action and stability. This existing closure
retains multiplication on both sides and all derivative descendants, together
with linear divergence-range IBP. The paired Weyl entry packages that route
for its fixed kinetic equations. New interactions retain their own stability
obligation.

## Use The Same Operations

After constructing P with any of these routes, use:

```lean
P.Coefficient
P.Source
P.residual
P.projection p
P.coefficientEquiv f
P.extraction f p
P.reconstruction q p
P.nonzero_iff
P.forbidden_iff
```

`Coefficient` is the original relation-annihilating coefficient input; `Source`
is the linear relation quotient. `coefficientEquiv` has both inverse laws.
Extraction/reconstruction are quotient evaluation, and the last two criteria
are necessary and sufficient for the specified represented source and relations.
They do not enumerate the residual Hom space or infer a physical interaction.

The [mixed control](../../../Math/RepresentationTheory/DerivativeInterfaceControls.lean)
and [actual scalar factory](../../../Physics/FieldTheory/Jets/ScalarDerivativeInterface.lean)
compile with exactly these dot-operations. Graded and equations factories prove
agreement with their existing inputs/maps. Thus the source data stay appropriate
to the purpose while callers learn one set of operations.

## Select A Source Subspace

For a submodule V stable under P's action, use `S := P.select V hV` and the same
operations on S. Its relation is the preimage of the *full* relation module,
so a relation passing through other degrees is retained. `P.selectionEquiv V hV`
identifies S.Source linearly with its actual image in P.Source.

A global coefficient restricts via `P.restrict V hV f`, with evaluation preserved.
This is a restriction map; no extension of every selected invariant coefficient
to the full source is asserted. Distinct selected degree images may overlap.
Neither direct-sum independence nor invariant-complement existence is assumed.

The scalar example packages `ScalarDerivativeInterface.selected lambda` for
the invariant span of `box phi` and `phi^3`. Its selected coefficient law is
`f(box phi) + lambda*f(phi^3) = 0`; no EOM term is discarded by selecting this
source. The factory also supplies the full-quotient image equivalence.

## Input Burden And Existing Routes

The graded factory takes the same six configuration arguments as the existing
uniform mixed entry and adds no proof obligation. The generic equations factory
retains its four data/certificate arguments. Each is supplied once to construct
P, after which operations use P. The actual scalar factory still needs only the
coupling. The represented Higgs entry takes a,b; the paired Weyl entry fixes
its kinetic expression. Both already include their equations and stability.
Generic selection needs V and its stability; the scalar selection
example packages both. These are compiled usage comparisons, not a measured
user-study result.

`Math.MixedOperatorInput` and all earlier derivative adapters remain available
as lower-level routes. `gradedInputEquiv`, `graded_map`, `equationInputEquiv` and
`equations_map` certify agreement with them. The finite local/statistical route
below retains its own contraction data; it is not mandatory for a represented
source. No optional mode flag or dummy EOM input is required by `graded`.

## Finite Coordinates On A Represented Source

After constructing P, an optional
[`Math.FiniteDerivativeCertificate.Presentation P`](../../../Math/RepresentationTheory/FiniteDerivativeCertificate.lean)
uses a finite basis of U for `P : Input H U`, before quotienting, and a
relation family with a proved span equality to `P.relations`. On an infinite
jet carrier, first choose a finite stable subspace with `P.select V hV`,
keeping its full relation preimage. Given such a presentation C,
`C.equivalence` gives inverse
maps between `P.Coefficient` and its annihilating, full-group invariant
coordinate vectors, with actual source evaluation reconstructed.

This route uses the represented source basis directly. Basis and relation-span
data are required only for this optional coordinate certificate; the ordinary
graded and EOM inputs retain their existing arguments. A matrix or raw probe
alone does not establish the relation or full-group obligations. See the
[complete scalar controls and remaining basis gates](../derivative-literature-foundations/finite-certificates.md).

## Finite Local Coordinates

Keep the original data: local and residual representations, contractions,
probes, normalization, invariant completeness, exchange maps and signs.
`FiniteLocalExtraRelations.inputMap` computes the coordinate input from them.
Supply T as a submodule of the actual tensor source, rather than a matrix
claimed to represent IBP. The adapter transports T through this computed map.

The resulting coefficient is a subtype of the existing statistical coefficient
space. `extraction` evaluates the descended coefficient on the image of an
actual source vector. `reconstruction_tmul` recovers a tensor coefficient as
the original contraction sum with the new quotient classes. `nonzero_iff`
is a necessary/sufficient existence statement for these constraints.
`emptyEquiv` recovers the original coefficient type when T is bottom.

An actual source must have the claimed factorized presentation before using
this finite-local route. This adapter does not automatically factor arbitrary
jet tensors into local and flavor factors. If such coordinates are unavailable,
the represented-source route still works without them; it does not manufacture
a local contraction basis. A proved source representation equivalence can
transport actual relations into the tensor source. The complete worked example
is [JetAdapterControls](../../../Math/RepresentationTheory/JetAdapterControls.lean).

## Lower-Level Jet Adapters

`JetInputAdapter.Input` uses the same stable relation/Hom vocabulary as the
published interface. `legacyInputEquiv` is a reflexive equivalence with the
old `RelationQuotient.vanishing` type. Its extraction and reconstruction are
ordinary quotient evaluation. For mixed jets, `mixedLegacyInput` accepts the
old positive-grade input and `mixed_legacy_map` proves agreement of maps.
`zero_evaluation` proves coefficient agreement on the original zero-jet source.

The positive-grade mixed route takes a source grade of derivative degree
`d+1` and currents of degree d. IBP is the actual divergence range, a linear
submodule. It is not its ideal closure. For the complete one-direction mixed
example, `JetAdapterControls.admissible_iff` and `finite_admissible_iff` show
the same relation in direct and finite-local inputs.

## EOM Route

The optional [local polynomial Lagrangian helper](../local-lagrangian-helper/input-guide.md)
generates seeds and first-variation currents before this route. Direct EOM
input remains available with the same arguments and operations.

Provide derivatives D and the seed set R. The existing differential ideal
construction includes products and all descendants. The combined relation is
that full ideal, viewed linearly, plus the actual divergence range. The input
condition in `equation_admissible_iff` is exactly:

- f annihilates every element of the differential EOM ideal;
- f annihilates every actual total derivative D_i(p).

Checking f only on the initial seeds is insufficient for this linear-functional
condition. Residual stability can be derived from existing EOM invariance and
derivative covariance, as in the [actual Lorentz scalar adapter](../../../Physics/FieldTheory/Jets/ScalarInputAdapter.lean).
No supplied Lagrangian or first-variation identity is required.

For a mixed algebra, `TwoSidedDifferential.combined` supplies the corresponding
full two-sided equation closure plus the linear divergence range. A common
`Input` packages that submodule and its stable action. Seed covariance,
multiplicativity and derivative covariance can establish stability through
[`TwoSidedCovariance.combined_stable`](../../../Math/RepresentationTheory/TwoSidedCovariance.lean).
The [paired Weyl construction](../../../Physics/FieldTheory/Jets/PairedWeylInput.lean)
provides the actual worked input. Its generated/direct relation equality and
inverse coefficient maps are in
[PairedWeylGeneratedInput](../../../Physics/FieldTheory/Jets/PairedWeylGeneratedInput.lean).

For nonlinear equations, retain the full source unless a separate theorem
justifies a graded decomposition. The scalar identity between `box phi` and
`lambda*phi^3` explains why independent fixed-degree coefficient inputs cannot
be imposed unconditionally. EOM may also constrain nonderivative operators;
`MixedOperatorInput` supplies the uniform off-shell/IBP route; its zero-degree
compatibility is not an on-shell identity. The full EOM route uses the same
stable relation/Hom vocabulary on the whole algebra and retains the mixing.

The same [model checks](../../../Physics/FieldTheory/Jets/NonDerivativeModelChecks.lean)
evaluate free nonderivative scalar powers and select the Higgs potential
span rho squared/rho cubed in the actual generated input. For the interacting
scalar, a cubic value c extends to a global coefficient exactly when
lambda*c=0. At lambda=1, c=1 the extension is rejected. Use this distinction
when choosing between the zero-degree off-shell entry and the full EOM entry.

The [additional verification](../derivative-literature-foundations/extended-checks.md)
also checks actual Lorentz Weyl mass/scalar-Yukawa old/new inputs and a
forbidden one-Weyl sector. Optional
[`InputPresentation`](../../../Math/RepresentationTheory/InputPresentation.lean)
maps preserve quotient evaluation when the action and complete relation
module are transported together. Nonzero seed scaling and invertible row
addition preserve the full EOM/IBP module. Supported real-coupling scalar
and paired Weyl reality checks are supplied separately; conjugation is not
automatically available for arbitrary caller equations or complex couplings.
