# Pinned Source And Convention Dictionary

[Li et al., arXiv:2201.04639v2, PDF page 38](https://arxiv.org/pdf/2201.04639v2#page=38)
was inspected visually. The LLHH expression is section 4's
`GenerateOperatorList[SMEFT,5]`, `Out[7]`, not an appendix D equation.
It contracts two weak epsilons between the lepton and Higgs indices and the
two left-handed leptons into a Lorentz scalar, with symmetric L flavor type.
The paper provides candidate data; its completeness assertion is not an axiom.

We use field order L,L,H,H, normalized `eps2` for weak and left-spinor
brackets, and the same Higgs direction h in the printed polynomial:

```text
paperLocal(x,y,h,s,t) = eps2(x,h) eps2(y,h) eps2(s,t).
polarizedLocal(x,y,h0,h1,s,t)
  = (eps2(x,h0) eps2(y,h1) + eps2(x,h1) eps2(y,h0))/2 * eps2(s,t).
```

The second formula defines the symmetric bilinear polarization of the printed
Higgs polynomial, not an unnormalized sum. `diagonal_local` proves agreement
when h0=h1. Exchanging complete leptons reverses the spin bracket; the weak
factor and flavor functional are symmetric. The resulting coefficient is
alternating in leptons and symmetric in Higgs fields. There is no four-fermion
alternatization and no extra factorial from two bosonic slots.

The pure probe x=y=e0, h0=h1=e1, s=e0, t=e1 returns the residual coefficient
with factor one. A mixed weak probe returns -1/2, explicitly testing polarization.
Symmetric flavor basis coordinates evaluate on `SymmetricPower.tprod [bi,bj]`;
off-diagonal pairs are not counted twice and no hidden factor two is inserted.

This is a normalized local operator interpretation. It does not certify
ABC4EFT runtime output arrays, a general p-basis algorithm, or the
amplitude/operator correspondence. No physical conjugation identification is
needed for this left-chiral LLHH candidate. Actual-field applications use the
existing explicit equivariant lepton/Higgs `Inputs` identifications.
