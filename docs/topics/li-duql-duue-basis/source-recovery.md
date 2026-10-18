# Pinned Source And Convention Dictionary

The local PDF of [Li et al., arXiv:2201.04639v2](https://arxiv.org/pdf/2201.04639v2)
was inspected visually on PDF pages 50 and 52, not only through extracted text.
The paper supplies the following expressions, not a completeness axiom.
Its appendix explicitly distinguishes on-shell amplitude bases from operator
bases. We certify a normalized local interpretation, not that correspondence.

## DUQL: D.37, PDF Page 52

Paper order: `L Q d_C† u_C†`. Local factors:
`epsilon(a2,a3,a4) epsilon(i1,i2) <12>[34]`, with independent flavor slots.
Repository order: D,U,Q,L. The permutation of paper positions is (3,4,2,1),
which is odd. Color cycling is even; weak and left-spinor bracket reversals
each contribute a minus and cancel. The surviving Fermi minus is compensated
by source `-k`. The direct contraction then has the standard repository
normalization, and distinct-species raw alternation has no repeated-slot factor.

## DUUE: D.6, PDF Page 50

Paper order: `d_C e_C u_C u_C`. The symmetric-U flavor component multiplies
`epsilon(a1,a3,a4) <13><24>`, and the alternating-U component multiplies
`epsilon(a1,a3,a4) <12><34>`.

The existing positive-degree repository DUUE sector uses right spin and
fundamental color. We interpret the conjugate local expression in normalized
right-spinor coordinates. `conjugate_symmetric` and `conjugate_alternating`
prove conjugation of the scalar local factors. They do not identify arbitrary
flavor representations with their conjugates. A physical model must supply
that identification; the existing signed-sector conjugation API also requires
an equivariant semilinear species-reversing involution.

Repository order is U,U,D,E. The D,E,U,U reorder is even, as is the color cycle.
The two local seeds become cross and direct spin pairings respectively.
Under U exchange the color sign cancels the Fermi sign. For unrestricted
residual k, the actual source functionals are

```text
S = -(k + swap k)/2
A =  (k - swap k)/4.
```

S is symmetric and A alternating. Raw two-term exterior alternation reconstructs
the ordered coefficients `(k, -k-swap k)`. Thus both printed types are needed
for general flavors; assuming symmetric U would lose allowed coefficients.

## Shared Four-Family Consumer

The four-family product uses direct supplied multiplicity carriers. QQUE's
earlier dual-coordinate certificate is not silently identified with arbitrary
carriers. `LiFourFamilyCertificate.qque_literal` verifies its D.38 local
formula directly in this shared convention, with the E,U bracket reversal
and Fermi sign explicit. QQQL uses its proved literal-seed inverse.
DUQL/DUUE candidates are transported through their residual equivalences into
the independently derived full signed-species decomposition. The composition
has both inverses. This does not infer physical dagger identifications or
equate package-specific arrays.
