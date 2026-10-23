# Full Higgs Coefficient Connection

## Proven input transport

[TwoSpeciesCoefficientBridge](../../../../../Math/RepresentationTheory/Coefficients/TwoSpeciesCoefficientBridge.lean)
constructs a fixed-content full symmetric field coefficient equivalence to
coefficients on two separate symmetric powers, for arbitrary species module
types and actual group representations. The source consumer retains an
arbitrary already statistical source through invariant tensor currying.
There is no finite-dimensional, semisimplicity, seed or unproved equivalence
premise in this transport.

[TwoSpeciesPattern](../../../../../Math/RepresentationTheory/Content/TwoSpeciesPattern.lean)
proves the canonical pattern's exact species counts, its orbit/count iff and
the decomposition of its stabilizer into independent block permutations.
[TwoSpeciesSymmetricDescent](../../../../../Math/RepresentationTheory/Symmetric/TwoSpeciesSymmetricDescent.lean)
implements dependent type transport and proves the compatibility/symmetry
iff and both quotient descents. The previously proved normalized full typed
reconstruction is reused; both inverse identities and covariance are checked.

## Full-group weak constituents

[CharacterTwistTransport](../../../../../Math/RepresentationTheory/Constructions/CharacterTwistTransport.lean)
and [TwistedSU2ClebschGordan](../../../../../Math/RepresentationTheory/SU2/TwistedSU2ClebschGordan.lean)
transport an actual pulled-back doublet with scalar character chi. Each
constituent retains chi^h * chi^(-d) and weak degree h+d-2r, with
0 <= r <= min(h,d). The group and character homomorphisms are explicit
input data; the constituent action correspondence is proved, not assumed.

[SMHiggsConstituents](../../../../../Physics/StandardModel/Operators/Support/Coordinates/SMHiggsConstituents.lean)
discharges these data for the original SM Higgs action, including its
hypercharge-circle character z^3. [FullHiggsCoefficientBridge](../../../../../Physics/StandardModel/Operators/Higgs/FullHiggsCoefficientBridge.lean)
connects the original scalar species with neutral one-dimensional
multiplicities, an arbitrary source and the full constituent representation.
Its matter consumer retains actual signed SM fields at every exterior degree
and supplied flavor actions. Its weak-singlet corollary requires precisely
the existing whole-source weak-triviality condition.

## Boundaries

These are coefficient-space presentation equivalences and exact transports
of allowance/prohibition. They do not themselves decide all source Hom
supports or establish a uniform primitive-degree bound. Higgs multiplicities
and residual Higgs actions outside the specified class require their own
input construction. No interaction, UV realization or rate follows from
the existence of a coefficient-space constituent.

The [topic result](../../../../topics/sm-support-and-lfv-decomposition/full-higgs-connection-results.md)
records the complete bounded endpoint and verification.
