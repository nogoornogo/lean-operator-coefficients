# Fixed Signed Convention Result

The [plan](signed-plan.md) is complete for the supplied Euclidean convention,
one N and u,d,s. The [source](../../../Physics/StandardModel/Operators/DevMohapatraSignedConvention.lean)
reuses the existing charge matrix, right projector, exterior algebra and exact
selected-channel tree elimination; no new matching foundation is introduced.

## Proven dictionary

Writing C for the existing charge matrix, the explicitly defined -C is both
its left and right inverse. Its projected two-spinor Grassmann bilinear is
minus the existing epsilon bilinear. Thus a positive M/2 inverse-C Majorana
term becomes -M N0 N1; each inverse-C vertex translates its coupling to its
negative. The epsilon-contracted down current is translated independently.
The literal product of three inverse-C bilinears is minus the existing
printedOperator.

Consequently generated(m, M, -lambda, -b) equals
-treePrefactor(m, M, lambda, b) times inverseOperator. Here m is the supplied
scalar quadratic parameter, not an inferred signed physical mass convention.
The two vertex sign changes cancel in the squared numerator, while the
three-bilinear target retains a minus sign. This proves the signed coefficient
in this particular dictionary, not the sign of the paper's coefficient.

For nonzero c and M, consistently multiplying every bilinear by c changes
the scalar prefactor by c cubed: the Majorana parameter and both couplings
all acquire c. The target's three bilinears also acquire c cubed. A bilinear
phase or normalization therefore must be transported through the action and
target together; changing only the target is not a matching comparison.

## Boundary

The paper's suppressed charge-conjugation phase, chirality and canonical
kinetic dictionary are still not uniquely recovered. The ordered versus
independent down-flavor sum remains a separate factor-four choice described
in [the inspection](convention-results.md). No full Hermitian/Minkowski action
translation or full polynomial-to-physical-intertwiner identity is proved.
Existing conditional kinetic and Grassmann pairing tools may help a future
explicitly chosen dictionary; they do not establish the missing paper inputs.
The earlier norm-level conditional discrepancy is not upgraded to a certified
paper error. No rates, loops, new flavors or additional N are included.
