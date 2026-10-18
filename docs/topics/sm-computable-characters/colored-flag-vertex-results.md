# Positive flag diagrams and actual restricted color vertices

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. This continues the
[contraction plan](colored-contraction-plan.md) after
[raw coefficient spanning](colored-contraction-results.md). Original endpoint
2 remains open at diagram/source assembly and its complete q/l consumer.

## Uniform positive flag criterion

`ColorFlagNonvanishing` uses the polynomial chart

```text
v_i = (1, x_i, y_i),    f_i = (-u_i*x_i-y_i, u_i, 1).
```

It proves incidence `f_i(v_i)=0`, and nonzero actual vectors and linear
functionals at every specialization. Evaluations between distinct vertices
and the vector/covector determinants on three distinct vertices are nonzero
polynomials. Every finite product of those factors is nonzero in the
polynomial domain, and mathlib's infinite-field polynomial extensionality
supplies a simultaneous complex specialization.

`nonzero_iff` proves the precise positive graph condition for this chart:
there exists a specialization making the complete graph evaluation nonzero
iff every pair joins distinct vertices and every determinant uses three
distinct vertices. Graph size and vertex set remain symbolic. Repeated
vertices and self-pairs vanish by alternating determinants and incidence.
This is an algebraic existence theorem, with no content enumeration,
numerical rank or multiplicity calculation.

## Actual symmetric and trace-free sources

`SymmetricTensorSplit` proves a canonical equivariant retraction from raw
tensor powers onto symmetric powers. The normalized section sends a pure
power to the corresponding pure tensor and is fixed by every slot
permutation. The degree remains arbitrary.

`SymmetricTensorTrace` proves that a single raw vector/covector contraction
after that symmetric inclusion equals the included symmetric trace.
Injectivity of the lower-degree inclusion gives an exact zero iff. The
proof uses the existing polarization span, with no chosen tensor basis.

`RestrictedColorTraces` compares this normalized trace with the actual
quadratic/dual, cubic/dual and quadratic/dual-quadratic contractions already
used in Q branching. Their symbolic scalar factors are 2, 3 and 4. Thus
every vector in the actual three kernels has zero single-slot raw trace.
Explicit incident pure flag vectors belong to each kernel.

`RestrictedColorVertices` supplies actual raw-tensor split retractions onto
these kernels. It proves the source embedding formulas, trace exclusions
and exact raw pure-tensor images of those flag witnesses. These are full
group-equivariant source maps, not supplied occurrence comparisons.

## Contragredient components

`SymmetricPowerDualEquivalence` proves perfect symmetric-power duality in
arbitrary finite dimension without irreducibility. The existing descended
symmetric pairing agrees with the raw perfect tensor pairing on normalized
sections. This proves injectivity; the already proved symbolic symmetric
dimension identity gives surjectivity. No exact dimension is evaluated.

`KernelDualComparison` cancels a proved common finite summand after actual
source/quotient duality. Its interface accepts the original additive-monoid
structures and constructs the groups needed for cancellation internally;
this avoids expanding carrier dictionaries while comparing representations.
`RestrictedColorDuality` applies it to all three actual contraction kernels
and to trace-free endomorphisms. The latter retains the existing nonzero
dimension hypothesis, discharged for defining color by its proved dimension.
No irreducible classification or new literature premise is supplied.

## Remaining connection

The flag criterion is not yet the all-content support theorem. The raw
evaluation/volume spanning family must still be identified with diagrams
on grouped vertex slots, including the determinant-block evaluation formula.
Invalid diagrams must be shown to vanish on every actual source vector,
using the proved symmetry and trace properties. The flag witnesses then
give the converse for valid diagrams. Bidual/slot transports, simultaneous
weak/left/right spin labels and the all-degree Higgs/q/l consumer remain
part of that assembly. No coefficient nonzero test may remain at the final
classification endpoint.

See [verification](colored-flag-vertex-verification.md).
