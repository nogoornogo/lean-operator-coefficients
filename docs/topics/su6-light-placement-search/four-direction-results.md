# Four Bounded Change Results

The [frozen four-direction plan](four-direction-plan.md) was executed with
[exact finite checks](../../../tools/su6-light-placement-search/check_four_directions.py).
These are computational screens, not new Lean certificates or full UV models.

| Direction | Exact domain | Outcome |
| --- | --- | --- |
| VEV / mass direction | Six basis covectors in the 27-component coordinate mass | Rank 12 in each case; only direction six preserves all tested standard SM Lie generators |
| Scalar / mass completion | All symmetric matrices respecting the supplied hypercharge Lie generator on the same fields | 29 permitted upper-triangular entries; every Q,u^c,e^c row has no opposite-hypercharge partner, so all ten components remain light |
| Added matter / split placement | Two fifteens and one conjugate fifteen, Z4 scalar copy charges; 64 charge triples times eight Q/u^c/e^c pairing choices | 56 pass selected mass/charge gates; 24 split placements, all with equal copy charges; none charge-forbids qque |
| Outside scalar/block residual action | C4, Q/e^c neutral and u^c phase i, all other baseline fields neutral | SM Lie/mass gates pass and the actual qque polynomial has charge 3; specified root-diagonal inner UV covariance fails |

## VEV and scalar screen

The changed covector explicitly changes the symmetric component mass: each
fifteen component involving that direction pairs with a dual-six component,
and the two corresponding dual-six singlets pair. Color/weak rotations and
hypercharge are checked on the resulting matrix. These six representatives
do not exhaust arbitrary VEVs or gauge-conjugate embeddings. Choosing a new
SM embedding is not part of this test.

The scalar screen is deliberately permissive: it allows every symmetric
mass entry compatible with hypercharge, rather than assuming a particular
small scalar multiplet or potential. Invariance imposes `(Yi+Yj) Mij=0`.
The supplied Q,u^c,e^c component charges have no opposite charge anywhere
in this 27-field carrier. Thus the row-zero conclusion covers this entire
coordinate matrix family, independent of remaining color/weak constraints.
It is not merely a list of sampled masses. It has not been promoted to a
new Lean theorem or source-matched scalar construction. Existing symmetric
scalar completion provides motivation for considering arbitrary bilinears,
not a claim of a minimal physical scalar sector.

## Enlarged placement screen

A conjugate component must pair with a fifteen copy of opposite Z4 charge.
If different Q/u^c/e^c components pair with different copies, both copies
must have the same charge. Hence the surviving components still satisfy
`2qQ - qu - qe = 0`. The finite count concerns selected ten-sector pairing
choices, not 56 complete UV models or a classification of arbitrary copy mixing.
The two-copy scalar charges are explicitly restricted; gauge block factors
and non-Abelian actions are not enumerated here.

One neutral split representative is extended to an actual 57-component
symmetric matrix with 21 disjoint paired entries. Its exact Fraction rank
is 42, leaving fifteen zero modes. Each pair has opposite hypercharge.
This is a finite matrix example, not a full-group branching, Yukawa-origin
or residual-covariant UV certificate. No qque protection is found.

## Independent residual phases

The fourth candidate is a genuine diagonal order-four coordinate action.
It commutes with the tested standard SM generators and preserves the supplied
baseline mass. Every nonzero term of the existing Lorentz/Grassmann qque
polynomial has phase i cubed, so that named polynomial is charge-forbidden.
This is a useful broken-phase control, not all B1 prohibition.

Under a root-diagonal inner automorphism, every occurrence of rho(E03) would
have to acquire one common ratio. The candidate gives both ratios 1 and i,
failing that gate. This excludes the specified UV realization; it does not
classify arbitrary automorphisms, outer actions or larger fields. No other
UV action is invented to turn this into a protecting model.

## Endpoint and next useful work

Each authorized direction has a bounded concrete test. No protecting SU(6)
model has passed the UV/action/light gates. The most informative outcomes
are the absent opposite-charge partners in the original carrier and the
contrast between broken-phase qque prohibition and failed UV covariance.
Further useful work would require either a richer enlarged representation
that permits different residual-charge placement, or a specified broader UV
covariance realization of the fourth action. Neither follows from these tests.
The exploration stops at this recorded screen, without beginning unbounded
representation or automorphism classification.
