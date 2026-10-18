# Automorphism-Covariant SU(6) Model Interface

## Result And Meaning

The interface replaces strict UV commutation by ordinary complex-linear
covariance under a supplied group action by automorphisms. It supplies necessary
model data and a proved descent interface; it does not construct a protecting
model, solve a vacuum problem, or assert proton stability.

The [mathematical module](../../../Math/RepresentationTheory/AutomorphismCovariantHom.lean)
defines `Action a alpha`, requiring an actual residual representation and

```text
residual(h) local(g) v = local(alpha(h)(g)) residual(h) v.
```

`stable` proves that the span of local(g)v-v is preserved. `equiv` and
`equiv_mk` prove two-sided residual Hom descent through that independently
defined relation quotient. `forbidden_iff` equates complete invariant-map
vanishing with complete residual Hom vanishing. There is no finite-dimensional,
compactness or semisimplicity input to this mathematical result.

`commutes_of_identity` recovers strict commutation when alpha is the identity
homomorphism. The conjugation control and its faithful commutation criterion
show the hypothesis has been genuinely weakened. A persistent finite control
uses the regular representation of permutations of three letters over the
rationals and two noncommuting transpositions. It is not an SU(6) protecting
inhabitant and is not an outer-automorphism example.

## SU(6) Data And Proven Consequences

The [model module](../../../GUT/SU6/SelectionRules/Models/AutomorphismCovariantModel.lean)
retains an ordinary Abelian H and actual finite-dimensional continuous-unitary
SU(6) fermion/scalar representations. Each carrier has a jointly continuous
unitary residual action covariant under the same alpha. Individual SU(6)
automorphisms are continuous. Joint continuity of alpha itself is not asserted.

An injective continuous unbroken-gauge embedding K into SU(6) and an action
beta by automorphisms of K must satisfy normalization. The supplied vacuum is
fixed by K and by the scalar residual action. This permits zero VEVs and
additional stabilizers; it does not derive an exact SM stabilizer.

The complex symmetric bilinear mass is invariant under K and explicitly under
H. It is not required to be invariant under all SU(6). The mass and vacuum are
separate data: this endpoint supplies no Yukawa/scalar-family realization
linking them and no realistic mass/mixing conditions.

`radical_stable` derives H preservation of the actual mass radical, using
mass invariance and the inverse residual action. `lightAction` derives covariance
on actual light vectors, not just UV character support. `lightEquiv` applies
local relation-quotient Hom descent to this light carrier.

## Typed Target Certificates

`HasDualTarget` states equality of gauge dual characters on the actual radical
with a separately supplied target representation. `HasPositiveDualTarget`
requires a positive natural generation count and matches that many copies of a
supplied one-generation dual gauge character. Gauge singlets have zero dual
gauge index. These predicates do not identify a chosen target as SM by name.
An application must prove its field/embedding dictionary is the physical SM.
They do not exclude vectorlike or self-dual zero modes.

`HasResolvedDualTarget` compares ordered gauge-then-residual traces and their
duals with a supplied covariant target action. This exposes residual-resolved
matching without pretending the actions commute as a direct product.
Its target must be instantiated with the desired SM profiles and singlets;
no implication from gauge-only matching to resolved matching is asserted.
No existence or conservation theorem for these certificates is added here.

## Coefficient And Physical Boundary

`coefficientEquiv` applies the new descent to any independently supplied actual
covariant coefficient carrier under K and H. It does not construct the
fourth-exterior-power action, Lorentz action, local tensors, or its BNV support.
Consequently the previously commuting mixed-degree completeness theorem is not
silently reinterpreted as a theorem for all normalizing actions.

The next bounded implementation can construct a covariant dimension-six carrier
and its support, then solve the target and vanishing conditions for an explicit
candidate. Required Yukawa realization, SM matching, quantum exactness and
all-degree protection remain independent obligations. A nonzero allowed
coefficient would still not establish UV generation or a decay amplitude.

## Verification

Persistent strict audits:
[mathematics](../../../Math/RepresentationTheory/Audit/AuditAutomorphismCovariantHom.lean)
and [SU(6)](../../../GUT/SU6/SelectionRules/Audit/AuditAutomorphismCovariantModel.lean).
The topic record owns commands and final outcomes. Only the three standard
Lean axioms are permitted transitively; no new custom axiom or exception.


## Subsequent Exterior Bridge

The [exterior/support phase](exterior-result.md) now derives exterior covariance
and supported functional descent, with a degree-four actual-radical adapter.
This closes the abstract exterior-action obligation; a full Lorentz/SM BNV
presentation and a concrete protecting candidate are still required.
