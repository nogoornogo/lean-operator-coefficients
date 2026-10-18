# Action Translation Result: One Chiral And Kinetic Convention

## Result

The participating barred Yukawa action is translated into a single explicit
chiral convention, tracking Hermitian conjugation and canonical kinetic terms.
Neutral mass and colored vertex now use one source coupling dictionary. In
this canonical real-VEV reading a definite heavy-mixing magnitude discrepancy
with displayed Eq.(12) remains. The generated-coefficient mechanism remains
nonzero on the stated domain. This is not paper-wide validation or refutation.

Sources: [2211.02054v2 HTML](https://arxiv.org/html/2211.02054v2),
[versioned PDF](https://arxiv.org/pdf/2211.02054v2), Eqs.(2),(6),(7),(10)–(14),(24).

## Explicit Field And Kinetic Dictionary

[ChiralActionConvention](../../../Physics/FieldTheory/Mass/ChiralActionConvention.lean)
uses an associative noncommutative star algebra. Grassmann conjugation reverses
product order; odd conjugate and differentiated components anticommute.
Write a left spinor n=(n0,n1), and fix its charge-conjugate right spinor
r(n)=(-star(n1),star(n0)). This map has the explicitly proved inverse.

The four-component convention has left embedding (s0,s1,0,0), right embedding
(0,0,r0,r1), and gamma0 with off-diagonal identity blocks. The actual gamma0
barred product reduces to star(s0)*r0+star(s1)*r1. For odd components this is
star(bracket(s,n)), where bracket=s0*n1-s1*n0. Thus the Hermitian conjugate of
-y*zbar*barred(s,n) is -star(y)*z*bracket(s,n). Both generator order reversal
and complex coupling conjugation are essential.

For kinetic matrix A, the right kinetic density becomes the left density with
flip(A)=[[A11,-A01],[-A10,A00]], plus a formal total derivative. flip(1)=1 and
flip(sigma_k)=-sigma_k for all three explicit Pauli matrices. The common
factor i may be applied to both sides. Hence the standard right/left time and
spatial principal forms translate consistently with no norm-changing scale.
The complex component norm form is also preserved.

A Majorana four-spinor contains both chiral blocks. Its canonical kinetic half
reduces to the same one-Weyl kinetic density plus half the formal divergence.
Its barred product with a right field still contains exactly the original
bracket, without an additional vertex half or sqrt(2).

These are exact algebraic identities. Spacetime derivatives are represented by
formal differentiated components with explicit odd anticommutation; discarding
an integrated total derivative requires the usual boundary assumption, which
is not a theorem about a spacetime domain here. Canonical kinetic terms are
specified for this reading; they are not inferred from an unprinted full
Lagrangian or arbitrary noncanonical source metrics.

## Simultaneous Mass And Vertex Reconstruction

[ActionTranslation](../../../GUT/PatiSalam/Matching/ActionTranslation.lean)
uses original source couplings yR,yPhi, chosen real vR,w, h2=0 and the conjugate
Phi coupling yt=0. Define v=vR/sqrt(2) from the source VEV definition. The plus
Phi Yukawa and minus chi Yukawa give, in the fixed standard minus-mass action,

| Object | Fixed translated convention |
| --- | --- |
| Displayed barred colored chi vertex | -yR*star(chi_d)*barred(xi,dR) |
| Its holomorphic conjugate | -star(yR)*chi_d*bracket(xi,dR-conjugate) |
| Neutral holomorphic mixing | M=star(yR)*v |
| Selected holomorphic Dirac entry | d=-star(yPhi)*w |
| Canonical mu=0 matrix | [[0,d,0],[d,0,M],[0,M,0]] |

The Dirac minus records Eq.(6)'s plus Yukawa relative to the chosen minus mass
convention; a rephasing can change that sign and must also change the field
identification. No different coupling redefinition is used in the neutral and
colored vertices. The Majorana parameter is fixed to zero for the coefficient
consumer; no finite-mu diagonalization is claimed.

The parameter map into ModelApplication retains the original colored-vertex
yR, while M is star(yR)*v and the effective Dirac Yukawa is -star(yPhi).
This corrects a possible unchanged-coupling reading of the earlier abstract
component chart. The older SourceConnection theorem with M=y*star(v) remains
valid for its specified chart, but is not the literal complex source-coupling
identification established here.

The matrix action, exact normalized kernel, and actual exterior light
coefficient are connected by this map. On Lambda,m,yR,vR nonzero, the latter
is nonzero iff w,yPhi are nonzero and C_L or C_R is nonzero. Zero UV coefficients
still give zero. Canonical field phases and the supplied typed sector dictionary
must be retained when comparing scalar prefactors with Eq.(24).

## Definite Same-Convention Comparison

The exact Lean theorem is

```
norm(yR*vR) = sqrt(2)*norm(M).
```

For yR,vR nonzero, the two norms are unequal. Conjugating a coupling or changing
unit-modulus field phases cannot remove a magnitude discrepancy. The canonical
Majorana kinetic half and the symmetric mass-action half have been accounted
for explicitly; they do not provide this missing sqrt(2).

Therefore the displayed heavy mixing yR*vR is not the heavy mixing obtained
from Eqs.(2),(10),(11) under the single canonical convention specified here.
These expressions need a changed displayed factor or an additional, consistently
propagated field/kinetic/coupling convention to agree. A noncanonical field
normalization would change both the kinetic coefficient and the vertices and
must not be introduced only into Eq.(12).

This establishes a conditional internal formula discrepancy, stronger than the
previous overall-factor-only test. It does not establish what unpublished or
implicit conventions the authors intended, or that every claim in the paper
is false. In particular, a nonzero normalization factor does not eliminate
baryon violation, and this result does not calculate decay rates.

## Inputs, Boundaries And Stop

Proved: four-component barred/chiral reduction in the explicit gamma0 convention,
Hermitian-conjugate Yukawa relation, canonical kinetic identities modulo formal
divergence, Majorana kinetic/vertex factors, selected source parameter map,
normalized actual coefficient nonzero criterion, and magnitude mismatch.

Inputs: canonical kinetic form, odd-field/derivative algebra laws, selected
Higgs vacuum and coupling slice, higher C_X, previous SM sector admission.
Full PS group-equivariant branching, alternative noncanonical metrics, finite-mu
approximations, rates, hadronic amplitudes and UV origins are not verified.

The requested simultaneous action translation reaches a definite comparison
in this convention. No further search for a convention engineered to restore
agreement is active. A broader paper comparison would have to specify and
verify an alternative complete convention, including its kinetic action and
all affected vertices. See [verification](action-translation-verification.md).

## Common-Scale Follow-Up

The [common-scale result](common-scale-result.md) proves that a nonzero
common matrix factor preserves the local mismatch, distinguishes this
completed gate from full signed coefficient certification, and compares
the relevant published formulas. Independent field rescalings and arbitrary
kinetic metrics remain outside the theorem.
