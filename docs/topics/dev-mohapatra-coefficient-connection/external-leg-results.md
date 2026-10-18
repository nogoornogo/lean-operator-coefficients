# Fixed External-Leg and Conjugate-Completion Result

The [bounded plan](external-leg-plan.md) is complete. The
[Lean source](../../../Physics/StandardModel/Operators/DevMohapatraExternalLeg.lean)
provides a mass-inverse contraction independent of the sequential elimination
used to define the earlier generated action. It also proves a projection
identity for an explicitly supplied complexified conjugate completion.

## Independent mass-inverse route

For the chiral action -M N0 N1, the antisymmetric mass kernel and its inverse
are explicitly defined as

```
H = [[0, -M], [M, 0]]
H_inverse = [[0, 1/M], [-1/M, 0]]
S = [-g J1, g J0],  g = a b / m
L_sewn = (1/2) sum_{r,t} (H_inverse)_{r,t} S_r S_t.
```

Both inverse identities are proved when M is nonzero. `mass_action` proves
that the quadratic half and H give exactly -M N0 N1 for anticommuting odd
components. The cubic S entries are constructed directly from the u,d,s
fields and color down currents, not from the generated polynomial.

Using odd-current anticommutation, `sewn_current` proves
L_sewn = (g squared / M) J0 J1. `sewn_generated` then proves equality with
the earlier generated polynomial, and `sewn_uv` connects it to the explicit
UV action after sequential substitution. The fixed six-component determinant
probe evaluates the sewn polynomial to g squared / M; the literal epsilon
operator evaluates to 2 on that probe. Their coefficient ratio is therefore
the earlier (a b) squared / (2 m squared M), with the already proved inverse-C
sign translation in the [literature-informed evaluation](literature-evaluation-results.md).

This is independent at the mass-kernel contraction/formula level, not an
independent identification of the source's action. It uses the same declared
vertices and masses. No kinetic propagator, LSZ, momentum dependence,
functional integral or S-matrix normalization theorem is asserted.

## Independent fixed-leg diagnostic

The [finite contraction script](../../../tools/dev-mohapatra/check-fixed-leg-sewing.py)
does not import the polynomial elimination script. It enumerates individual
cubic source vertex terms and the two oriented inverse-mass contractions.
Separately it assigns the two legs of each species to the literal uu/ds/ds
operator slots and computes their Grassmann permutation signs.

The literal probe is 2, and the sewn probe is g squared / M in eight exact
rational cases: two coupling/mass settings, two scalar mass signs and two
flavor weights. Three inverse-C pair signs make the literal target probe -2;
the two vertex signs cancel. This reproduces the signed coefficient and
preserves the earlier magnitude ratios. This bounded check is evidence,
not a Lean premise or a complete six-particle physical amplitude calculation.

## Conjugate-completion projection

The explicit completion adds a conjugate Majorana mass block and two
conjugate vertex channels to the paired scalar action, **counting the scalar
quadratic term once**. Barred coefficients and variables are independent.
For an algebra homomorphism that maps the unbarred vertices to the chiral
ones and kills the barred external vertices, `completion_projection_free`
proves that the projected action equals the chiral action minus the remaining
free conjugate Majorana mass term. If the conjugate heavy variable also maps
to zero, `completion_projection` proves exact equality with the chiral action.

These are generic algebra-homomorphism identities, valid beyond the selected
probe. The zero-image hypotheses are explicit and are not inferred from an
unproved solution. They clarify which terms can survive a holomorphic
projection; they do not establish completeness of the original truncation.

## Stop and assessment

The independent route confirms the earlier mass-half, Grassmann sign and
selected coefficient accounting. No discrepancy between the two algebraic
routes was found. The provenance-backed magnitude difference with the paper
is unchanged, and remains conditional on the source dictionary.

The full Hermitian-action endpoint is **not** claimed. Still needed are an
actual anti-involution/field dictionary identifying the supplied barred terms
with H.c., and a proof that the full stationary elimination commutes with the
holomorphic projection (or an equivalent graded calculation). The projection
hypotheses alone are not that proof. Existing ExteriorConjugation concerns
semilinear coefficient transport, and ChiralActionConvention has a supplied
star-algebra interface; neither automatically establishes this full action
and stationary-solution bridge. We stop at the frozen scope rather than
start a new star/graded foundation project or certify its missing premise.

No loop calculation, rates, new flavors/N copies, physical-carrier identity,
author contact, master merge or remote push is included.

The subsequently authorized [Hermitian recalculation](hermitian-results.md)
replaces independent barred data by literal H.c. for the formal scalar
calculation and checks heavy elimination through degree six computationally.
The earlier projection theorem and its hypotheses remain unchanged.
