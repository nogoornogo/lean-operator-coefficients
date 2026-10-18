# Source Recovery And Local Dictionary

## Primary Source And Citation Role

[Li et al., arXiv:2201.04639v2](https://arxiv.org/pdf/2201.04639v2),
appendix D.9, PDF page 50, supplies the candidate expression, not a Lean
completeness premise. The PDF page was visually inspected; extraction alone
was not used to decide epsilon positions. The pinned author repository used
in the preceding qque pilot is optional supporting data, not executed software.

The type is `L Q^3`, ordered `L₁,Q₂,Q₃,Q₄`. Three flavor tensors labelled
`[3]`, `[2,1]` and `[1,1,1]` multiply the same contraction:

```text
C(f₁;f₂,f₃,f₄) ε(a₂,a₃,a₄) ε(i₁,i₃) ε(i₂,i₄) <12><34>.
```

These are distinct symmetry components; treating qqql as only the mixed
component would discard allowed operators.

## Repository Order And Signs

The existing order is `Q₁,Q₂,Q₃,L₄`. Moving L through three fermions contributes
minus one. In that order the weak contraction is minus weak pairing 1,
and the spinor contraction is minus the third pairing `(14)(23)`. The latter
is spin pairing 1 minus spin pairing 0 by the two-dimensional Schouten
identity. After the fermionic reordering the seed therefore has entries
`(1,0) = 1`, `(1,1) = -1`, and other entries zero. The initial investigation
mistakenly identified the third spin pairing with pairing 0; direct symbolic
Lean verification rejected that identification. The corrected local identity
is proved in `LiQqqlConvention.fermionic_reorder`. Descent and the published
flavor normalization are proved by the six-permutation exterior certificate.

## Verified Component Dictionary

Write the old local coordinates as `(a,b;c,d)`. The new coordinates are

```text
t = (2(a+d)+b+c)/6       u = (b-c)/2
s = a-(2(a+d)+b+c)/3     v = (a+d+2(b+c))/3.
```

The inverse is `(2t+s,-t+u+v;-t-u+v,2t-s-v)`. Adjacent exchanges act as
`(t,-u,v,s)` and `(t,-u,-s-v,v)`. Both inverses and both conjugacy equations
are proved in
[FourDoubletProductComponents](../../../Math/RepresentationTheory/Unitary/FourDoubletProductComponents.lean).

For residual functionals, the necessary and sufficient relations say that t
is symmetric, u alternating, `s(x,y,z)=v(y,x,z)`, v is symmetric in its last
two inputs, and `v(x,y,z)+v(y,x,z)+v(z,x,y)=0`. The physical exterior inverse
and this characterization are proved in
[QqqlFlavorComponents](../../../Physics/StandardModel/Operators/QqqlFlavorComponents.lean).

For the proposed seed the component coordinates are
`(-1/6,-1/2,1/3,1/3)`. These nonzero projections motivate retaining all three
flavor symmetry types. The general finite-flavor cardinality and both inverses
are now proved. `source = -T-U/3+V` reconstructs all three components through
the seed orbit; actual raw exterior descent equals the independent completeness
inverse. See the [completed dossier](../../proof/current/applications/Physics/LI_QQQL_BASIS.md).
