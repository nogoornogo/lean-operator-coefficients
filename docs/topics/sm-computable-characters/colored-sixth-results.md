# Complete Q sixth branching and conjugate transport

Continuation from `checkpoint 01` on `proof/sm-computable-characters`, integration
target `master`; no merge or push authorized. All source obligations of the
[sixth-degree plan](colored-sixth-plan.md) are now proved.

## Actual sixth-degree decomposition

`ColorWeakSixthSlices` proves the complete retained SU3 x weak-SU2 equivalences
of the four nonnegative spin-weight spaces. If B6, B4, B2, B0 denote exactly
the positive sums listed in the plan, the actual source comparisons are

```text
Lambda^6 A tensor Lambda^0 A = B6
Lambda^5 A tensor Lambda^1 A = B4 + B6
Lambda^4 A tensor Lambda^2 A = B2 + (B4 + B6)
Lambda^3 A tensor Lambda^3 A = B0 + (B2 + (B4 + B6)).
```

`ColorWeakSixthAssembly.equivalence` identifies the entire retained isotypic
modules, proves the odd-spin modules zero, and assembles a full source
equivalence with independent spin degrees 0,2,4,6. This gives all twenty
color/weak/spin components, including the two distinct E weak-2 summands at
spin degree 2. The source continuity, torus bound and complete isotypic
decomposition are constructed, not supplied as branching assumptions.

`SU3DoubleSpinSixth.positive` transports it to the established three-factor
group order. `GUT.SMQSixthBranching.positiveSixth` connects the actual
species-0 Q core.

## Conjugate species without a second branching calculation

Mathlib already proves
`exteriorPower.bijective_pairingDual` in
`Mathlib.LinearAlgebra.ExteriorPower.Basis`. The local
`ExteriorDualEquivalence.pairing` proves equivariance of this existing perfect
pairing by its determinant evaluation on pure wedges. Consequently
`equivalence` proves, uniformly in n,

```text
Lambda^n(V*) = (Lambda^n V)*
```

as actual representations. No basis, determinant value or numerical dimension
is evaluated, and the perfect-pairing theorem is reused, not an external premise.

`SU3DoubleSpinDuality` combines this with the proved weak/spin doublet
self-dualities to identify the actual dual-color Q core with the full dual of
the positive core in every exterior degree. The new Physics endpoints are

- `SMQSixthBranching.negativeSixth` for actual species 5;
- `SMQFifthBranching.negativeFifth` and `negativeSeventh` for actual species 5.

The negative factors are the actual full-group duals of the proved positive
branches, with the correct right-spin projection. This does not assume that
any harmonic color kernel is irreducible or discard its action.

## Remaining full-support obligation

These results close all previously open Q/conjugate-Q middle-degree source
comparisons; existing Pauli and complementary-duality theorems handle the
capacity and remaining complementary directions. They are decomposition
results and do not decide all tensor products of the retained color factors
across species and generations.

The compatible positive scalar-coupling criterion for general mixtures of
symmetric, adjoint and harmonic color factors, followed by its all-content q/l
consumer, remains open. Unknown color Homs, signed coefficient tests or a
list of source decompositions are not counted as that completed criterion.
Original endpoint 2 therefore remains the active continuation.

See [verification](colored-sixth-verification.md).
