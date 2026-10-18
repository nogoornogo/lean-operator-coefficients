# Actual Q quartic color/weak resolution

The quartic color/weak kernel resolution is proved on the actual Q and
conjugate-Q core representations, together with degree-eight complements.
This implements steps 1 and 2 of the
[structural continuation](colored-support-completion-plan.md).
Degrees five/six, general restricted color coupling and original endpoint 2
remain obligations. No numerical support table or multiplicity is evaluated.

Working branch `proof/sm-computable-characters`, resume base `checkpoint 01`,
integration target `master`; no merge or push authorized.
See [verification](colored-quartic-resolution-verification.md).

## The actual color factors and joint branches

Write C for defining color, W for weak and S for the independent spin
doublet. Define H by the actual equivariant contraction

```text
H = ker(Sym^2 C tensor C* -> C),
(a b) tensor f |-> f(b) a + f(a) b.
```

H is a specified color tensor kernel with a constructed projection,
section and complete complementary split. Its irreducibility or a color
tensor-product positivity rule is not an assumed input.
The complete quartic decomposition has the following thirteen summands.
Numbers in the last two columns are symmetric-power labels.

| Actual color factor | Weak label | Spin label |
| --- | --- | --- |
| C | 2 | 4 |
| Sym^2 C* | 0 | 4 |
| C | 4 | 2 |
| H | 2 | 2 |
| H | 0 | 2 |
| Sym^2 C* | 2 | 2 |
| C | 2 | 2 |
| C | 0 | 2 |
| Sym^2 C* | 4 | 0 |
| Sym^2 C* | 0 | 0 |
| C | 2 | 0 |
| H | 2 | 0 |
| Sym^4 C | 0 | 0 |

The Lean equivalence groups the two top rows, the six middle rows and the
five last rows into finite products; tensor products distribute over those
products by the existing actual `TensorProductSums` equivalences. Repeated
color factors with different joint labels remain distinct. No specieswise
singlet test or identification of the weak and spin actions is used.

`SU3DoubleSpinQuartic.positive` and `negative` are actual full-action
equivalences. In the negative version C is replaced by C*, with its actual
contraction kernel; canonical biduality identifies the double-dual factors.
`positiveEight` and `negativeEight` use proved complementary exterior
duality. `SMQQuarticBranching` transports all four equivalences to the
actual signed cores 0 and 5, preserving the independent left/right spin
projections. These are core decompositions; they are not an all-content
support iff or a search through residual assignments.

## Universal source identities

`SymmetricFourth22.equivalence` constructs, in arbitrary complex dimension,

```text
Sym^2(Sym^2 A) = Sym^4 A + K22(A).
```

The forward mixed shuffle and its reverse satisfy
`FG = 3 id - coproduct * multiplication` and
`GF = 3 id - delta22 * exteriorMultiplication`. The images and annihilation
relations are proved, giving actual inverses. The representation wrapper
retains every group action. When dimension is at most three, K22 is the
whole `Sym^2(Lambda^2 A)`, because its fourth exterior quotient is zero.

`SymmetricSquareContraction` constructs the displayed color contraction
in every finite dimension. Its section inserts the identity tensor and
divides by `dim(A)+1`; the composition identity follows from the rank-one
trace identity for arbitrary tensors, without a basis enumeration.
`DefiningTraceFreeProduct` expands the actual whole tensor source in two
ways and cancels its common finite defining summand. Together with the
actual SU3 exterior dualities this proves

```text
C tensor trace-free End(C) = H + Sym^2 C* + C,
Sym^2(Sym^2 C) = Sym^4 C + Sym^2 C*.
```

The corresponding dual-color statements are proved too.
`SymmetricSquareDual.equivalence` proves perfect symmetric-square duality
in every finite dimension, without the irreducibility hypothesis of the
older general-degree pairing API. Its proof uses the actual symmetric
sections and perfect tensor duality.

`DoubletQuartic` obtains the weak factors from the existing proved
Clebsch--Gordan equivalence and the universal quartic split. In particular
`Sym^2(Sym^2 W) = Sym^4 W + scalar` and
`Lambda^2(Sym^2 W) = Sym^2 W`; the latter follows by cancelling the actual
symmetric summands from the two complete tensor-square decompositions.

## Resolution of both gauge kernels

For A = C tensor W, trivial determinant and dimension six identify
`Lambda^4 A` with the dual of the already resolved square. Expand the two
actual quartic sources `A tensor Lambda^3 A` and
`Sym^2(Lambda^2 A)` using the proved cubic/square identities and the new
source identities above. Proved finite-summand cancellation then removes
that known fourth exterior quotient. `ColorWeakQuartic.kernel211` has six
color/weak summands; `kernel22` has five. The resulting `quartic`
equivalence has no remaining K211/K22 on the color/weak space.

All generic color equivalence parameters are discharged in the actual
positive/negative wrappers. There is no new external premise, Weyl input,
irreducibility assumption, dependency change, raised Lean limit, content
rank certificate or exact multiplicity calculation.

## Remaining endpoint

The fixed color factors above still require compatible **positive coupling
criteria** for arbitrary reachable mixtures. Naming H does not prove all
its further products irreducible or decide them. Q core degrees five/six
and their full joint color/weak resolution also remain open. Generation
splitting and the all-degree Higgs/q/l consumers are available, but they
must only be applied as a complete classifier after those occurrence and
coupling obligations are discharged.
