# Resolved Q cubic branches by universal hook maps and cancellation

This continues checkpoint `checkpoint 01` on `proof/sm-computable-characters`.
The [bounded plan](colored-middle-plan.md) is implemented through the Q
cubic hook resolution. The Q/conjugate-Q core degrees three and nine now
have complete labelled equivariant decompositions. Degrees four through
six and arbitrary restricted-Young color coupling remain open; the original
full q/l support endpoint is not complete.

## The actual six branches

Write C for defining color, W for weak doublet and S for the independently
acting spin doublet. `SU3DoubleSpinCubeResolved.positive` proves a complete
equivalence for `Lambda^3((C tensor W) tensor S)` with the following sum.
Every row denotes an actual tensor representation, rather than an unknown
Hom or an assumed constituent.

| Color component | Weak component | Spin component |
| --- | --- | --- |
| scalar | Sym^3 W | Sym^3 S |
| trace-free End C | W | Sym^3 S |
| scalar | W | S |
| trace-free End C | Sym^3 W | S |
| Sym^3 C | W | S |
| trace-free End C | W | S |

`negative` uses dual color, its actual trace-free endomorphism action and
`Sym^3 C*`. Complementary exterior duality gives `positiveNine` and
`negativeNine`. The existence of all embeddings, projections and inverses
is proved; no unclassified hook remains in these target spaces.

`SMQResolvedCubeBranching.positiveCube`, `negativeCube`, `positiveNine`
and `negativeNine` transport the results to actual signed core species 0
and 5. Weak, left spin and right spin remain distinct. This is a core
branching result, not an additional all-Higgs or residual-charge iff.

## Universal algebraic proof

`SymmetricCubeHook.split` proves

```text
A tensor Sym^2 A = Sym^3 A + Hook A,
Hook A = ker(A tensor Lambda^2 A -> Lambda^3 A).
```

It has no dimension hypothesis. Its two mixed maps send

```text
a tensor (b wedge c) -> b tensor (a c) - c tensor (a b),
a tensor (b c)       -> b tensor (a wedge c) + c tensor (a wedge b).
```

Their compositions are three times the identity minus the relevant cubic
coproduct/multiplication composite. These vector identities give explicit
inverses. `SymmetricCubeHookRepresentation.equivalence` proves equivariance
for every group representation. `DoubletCubicHook` identifies `Hook W`
with W using the proved top exterior volume and vanishing exterior cube.

`ExteriorCubeDoubletHook` expands the entire source
`(A tensor W) tensor Lambda^2(A tensor W)` by the proved square Cauchy split
and both cubic hook splits. It has six actual summands. The already proved
cubic Cauchy equivalence identifies the common exterior-cube part. After
equivariant reordering, cancellation leaves

```text
Hook(A tensor W)
  = (Lambda^3 A tensor W)
      + (Hook A tensor Sym^3 W)
      + (Sym^3 A tensor W)
      + (Hook A tensor W).
```

Finally the proved color identities `Lambda^3 C = scalar` and
`Hook C = trace-free End C` resolve the four rows, and tensoring the
independent S factor completes the Q cube.

## Reused proved cancellation theorem

`FiniteSummandCancellation.nonempty_equiv` proves, for any group G,
that an actual finite-dimensional common summand t cancels from an
equivalence `r + t = s + t`. Only t needs finite complex dimension;
neither compactness nor irreducibility is assumed.

The proof constructs the dictionary between actual intertwiners and
group-algebra module maps, including products. Finite complex dimension
implies finite length over `C[G]` by restriction of scalars. It then applies
the pinned **proved** theorem
`TauCeti.nonempty_linearEquiv_of_prod_linearEquiv_of_isFiniteLength` from
`TauCeti/RingTheory/KrullSchmidt/Cancellation.lean` (dependency commit
`b9e2e182804073eb92718b68a9baf37df8e189bd`). This is actual library reuse,
not a literature premise or a claim that an audited implication proves its
hypothesis. The source comparison and finite-length hypothesis are both
discharged in Lean.

Cancellation supplies an actual equivalence using classical choice. It
does not evaluate character coefficients, numerical multiplicities or
matrix ranks. No new axiom, dependency pin or proof limit is introduced.

## Remaining boundary

The color components here are specified actual functors/kernels; their
irreducibility is not an input or a new conclusion of this decomposition.
Classifying arbitrary mixtures of the symmetric, trace-free and higher Young color components
still needs a positive semantic coupling rule. The later
[trace-free word rule](colored-restricted-results.md) now decides arbitrary
tensor words of either actual trace-free orientation and their joint SU2
matching, with no remaining equivalence premise. The earlier complete
[exterior-word criterion](colored-middle-results.md) covers exterior
defining/dual leaves only and remains distinct from that larger problem.

Degrees four through six need additional quartic/higher skew-Young source
splittings and actual product-action decompositions. Neither cancellation
alone nor the pinned Schur-Weyl character shadow supplies those source
identities. They have not been inserted as hypotheses or replaced by
numerical certificates. These are the next theorem-level obligations.

See [verification](colored-cubic-resolution-verification.md).
