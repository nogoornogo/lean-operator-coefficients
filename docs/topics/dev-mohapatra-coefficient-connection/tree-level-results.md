# Bounded Tree-Level Result

## What Is Derived

[Tree-level source](../../../Physics/StandardModel/Operators/DevMohapatraTreeLevel.lean)
defines an explicit one-N, u,d,s chiral action in an exterior algebra. There
are three scalar color coordinates and two Majorana spin components. Write
`m = mChiSq`, `M = mN`, `a = lam`, `b = lamDS`, with m and M nonzero.

For color i, let

```
D_i = sum_{j,k} epsilon_{ijk} (d_{j0} s_{k1} - d_{j1} s_{k0})
A_i = N_0 u_{i1} - N_1 u_{i0}
J_r = sum_i u_{ir} D_i
L = -M N_0 N_1 + sum_i [m chi_i chiBar_i + a A_i chiBar_i + b chi_i D_i]
```

All fermion components anticommute. The Majorana mass term is exactly
`-(M/2) (N_0 N_1 - N_1 N_0)`; `majorana_half` proves its reduction.
The mass and vertex signs above are supplied conventions. chi and chiBar
are independent coordinates for the paired scalar quadratic term. This
calculation selects the holomorphic six-quark component; the Hermitian
conjugate vertices and kinetic/derivative terms are excluded from this action.
It is not a proof that a truncation of the full Hermitian action is complete.

`uv_after_scalar` derives `-M N_0 N_1 - g (N_0 J_1 - N_1 J_0)`, where
`g = ab/m`. `uv_sequential_on_shell` then derives `g² J_0 J_1/M` from
the explicit UV action, by substituting the scalar and N solutions.
The reusable noncommutative elimination lemmas prove completed-square and
stationary-variation identities; no commutative replacement of odd sources
or functional-integral assumption is used. Odd anticommutation of the cubic
currents follows from existing exterior-algebra identities.

The independently defined literal contraction is

```
O = sum_{i,l} (u_{i0} u_{l1} - u_{i1} u_{l0}) D_i D_l
```

Thus O expands into precisely the two color epsilons and three right-Weyl
epsilon pairs of the selected Eq.(4) contraction, in literal uu/ds/ds
Grassmann order. `printedOperator_eq` proves `O = 2 J_0 J_1`.
`generated_printed` proves the derived action coefficient

```
C_tree = (a b)^2 / (2 m^2 M)
```

Writing m = Mchi² yields `(a b)^2/(2 Mchi^4 MN)`. The coefficient b denotes
the actual selected d,s vertex in the displayed action, not an automatically
identified literature lambda-prime.

## Nonvanishing and Order Controls

The u,d,s fields have 18 independent color/spin Grassmann generators.
`generated_nonzero` proves a nonzero generated polynomial when both masses
and both selected couplings are nonzero. A six-component restriction and
determinant coefficient extractor prove the current-product evaluation 1
and literal O evaluation 2. This is a polynomial nonvanishing proof after
fermion statistics, not just a nonzero ordered multilinear tensor.

The prior `sourceExterior` uses U,D,U,S,D,S generator slots and evaluates
to -2 on the corresponding probe. Literal uu/ds/ds order moves the second u
past the first down field. `source_generator_order` proves that one-swap
minus sign. The new +2 control is consistent with that sign. The prior
unnormalized exterior intertwiner is retained; it has not been replaced by
an asserted equality to the new polynomial under a full carrier dictionary.

## Conditional Comparison with the Paper

The pinned [source](references.md), Sec.III Eq.(4), prints
`(lambda lambda-prime_12)^2/(16 pi² Mchi^4 MN)` for a route described as
tree-level in Fig.1 and the surrounding text. `paperPrefactor` records only
that scalar, not its derivation.

If the paper's masses, couplings, right-Weyl and operator normalization are
identified with this explicit action dictionary, `prefactor_comparison`
proves `C_tree = 8 pi² C_paper`; `prefactors_ne` proves inequality for
nonzero masses and couplings. This is a proved conditional mismatch, not a
confirmed error in the paper. No loop factor occurs in the declared
derivative-free quadratic elimination.

One convention ambiguity is now quantified: `ordered_flavor_sum` proves
that including both ordered entries ds and sd with antisymmetric couplings,
without a half, gives b = 2 lambda-prime_12. `treePrefactor_down_rescaling`
proves the quadratic change in the coefficient. An independent-pair sum or
an appropriately halved ordered sum instead gives b = lambda-prime_12.
Under the unhalved ordered-sum identification the ratio to the printed
scalar is 32 pi², by these identities. Neither convention is silently
attributed to the source. These finite convention changes do not generate
the printed inverse 16 pi² factor.

## Endpoint and Remaining Boundary

The authorized bounded endpoint is achieved: explicit chiral UV action,
sequential tree-level generation, literal contraction factor, statistics-aware
nonvanishing, and conditional printed-scalar comparison. The original
SM/Lorentz/parity coefficient-space certificate remains independently proved.

Still external: exact source C-inverse/four-component phase and normalization,
complete flavor-sum and conjugate-action dictionary, kinetic normalization,
and a full polynomial-to-physical-intertwiner matching identity. Multiple N
copies, higher derivative terms, loops, hadronic dressing, rates, neutrino
mass and baryogenesis are excluded. There is no paper-wide coefficient
certification or downstream numerical conclusion.

The [subsequent fixed-domain inspection](convention-results.md) recovers the
printed scalar/conjugate-scalar placement and Majorana half directly from PDF
and TeX. Those particular source facts are no longer ambiguous. It does not
recover the remaining signed C-inverse, flavor-sum and kinetic/action dictionary
or discharge the full Hermitian-action or physical-polynomial bridge.
