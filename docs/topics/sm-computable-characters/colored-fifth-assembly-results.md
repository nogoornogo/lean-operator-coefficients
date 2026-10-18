# Complete Q fifth and complementary seventh branching

Continuation from `checkpoint 01` on `proof/sm-computable-characters`, integration
target `master`; no merge or push authorized. This assembles the
[proved fifth-degree slices](colored-fifth-slices-results.md) into a complete
actual exterior-source equivalence.

Write B1, B3 and B5 for the retained color/weak positive sums in that result.
`ColorWeakFifthAssembly.equivalence` proves

```text
Lambda^5 (independent-spin doublet external (C tensor weak doublet))
  = (Sym^1 spin external B1)
    + (Sym^3 spin external B3)
    + (Sym^5 spin external B5).
```

The fourteen color/weak/spin components are explicit in B1, B3 and B5. The
canonical complete SU2 isotypic decomposition is constructed from the proved
continuity and torus bound. Consecutive actual weight spaces and finite-length
cancellation identify its entire retained multiplicities. Even-spin spaces
vanish by the proved exterior parity condition, not a computed dimension.
Explicit forward and backward maps then assemble the full representation.

`SU3DoubleSpinFifth.positive` transports this complete equivalence to the
established color/weak/spin factor order on the actual Q core.
`positiveSeven` gives its complementary seventh degree by the existing
determinant-one exterior duality.

The Physics endpoints are

- `GUT.SMQFifthBranching.positiveFifth` on the actual signed species-0 core;
- `GUT.SMQFifthBranching.positiveSeventh` on the same core, with the dual
  complementary retained representation.

No branching, matching, irreducibility or Weyl premise is supplied. No
numerical dimension, multiplicity, matrix rank or character value is evaluated.
The new generic `SU2IsotypicIdentify` and `ZeroSummands` interfaces retain
the exact actual subrepresentations and can be reused at sixth degree.

This completes positive-Q core degrees five/seven. Sixth degree, the
conjugate-species transports, and the general compatible positive
restricted-color coupling rule remain active obligations. Consequently the
original complete mixed-content q/l support endpoint 2 remains open.

See [verification](colored-fifth-assembly-verification.md).
