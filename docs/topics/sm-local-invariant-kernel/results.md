# Matrix Connection Checkpoint And Stop

## Proved interfaces

`Math.FiniteInvariantKernel` specifies, for a representation rho, a finite
carrier basis b and a supplied finite family of actual group elements g_i,
the matrix

    A[(i,j),k] = coordinate_k(rho(g_i) b_j) - delta_(k,j).

`constraints_apply` proves that multiplying by functional coordinates gives
exactly f(rho(g_i)b_j)-f(b_j). `mem_kernel_iff` proves the kernel is exactly
the functionals invariant under the supplied tests, at every carrier vector,
not just on the basis probes. `equiv` constructs both directions between
actual group-invariant coefficients and this kernel when the tests are
proved exhaustive. `allowed_iff_rank_lt` proves nonzero coefficients iff
the rank of this constraint linear map is less than the number of columns.
The exhaustive-test premise is explicit in this generic interface.

`Math.GeneratorInvariantTests.invariant_iff` proves an algebraic generating
family is exhaustive, via the subgroup fixing a functional. It does not
infer generation from irreducibility or finite sampling.

`Math.PolynomialInvariantTests.zero_of_samples` proves degree-D polynomials
are determined by more than D distinct exact samples. `grid_zero` proves
the iterated two-variable version with separately bounded outer degree and
coefficient degrees. `exhaustive` composes a proved one-parameter polynomial
action identity, degree bound and actual generating-family certificate into
exhaustive finite tests. The action identity/degree bound remain premises;
no arbitrary representation is claimed to be polynomial.

## Actual Weyl discharges and control

`GUT.WeylGeneratorTests.generates` discharges algebraic generation for the
actual SL(2,C) group using the pinned TauCeti field transvection theorem.
`invariant_iff` applies to any representation of that actual group, including
the paired left/entrywise-conjugate-right action. No replacement by two
independent formal SL2 factors or a Lie kernel is made. Its transvection
parameter still ranges over C, so this is not itself a finite matrix.

`GUT.WeylFiniteKernelControl` completely discharges the finite test premise
for one actual left Weyl spinor. The two specified tests are the upper and
lower actual transvections at parameter one. Testing on the opposite basis
vector forces each coordinate functional value to vanish. The module proves
the full actual-group coefficient/kernel equivalence and that this kernel
is zero. This is an unconditional concrete control of matrix orientation
and reconstruction, not a certificate for every SM statistical content.

## Checkpoint boundary, subsequently discharged

At this checkpoint, the finite matrix for every SM source/constituent had not
been constructed. In particular, the generic exhaustive-test premise had not been discharged
for the actual SU(3) color factor. The pinned sources inspected at this gate
were local SmallSpecialUnitary, mathlib LinearAlgebra.UnitaryGroup, and
TauCeti LinearAlgebra.Matrix.GeneralLinearGroup.SpecialUnitary / Matrix.UnitaryGroup.
They provide actual matrix membership/actions, a subgroup presentation and
defining SU(3) irreducibility, but no inspected theorem proving that a chosen
plane-SU2 parameter family generates all actual SU(3).

The precise next structural prerequisite for the selected direct-group
route was an explicit actual family of two-coordinate determinant-one
unitary rotations, together with

    Subgroup.closure(range planeFamily) = top in actual SU(3).

It needed its own group-decomposition construction milestone. The finite
sign/permutation matrices used to prove defining irreducibility do not
already supply that generation or exhaustive higher-tensor test premise.
Using SL3 shears instead would require the separately unproved invariant
correspondence and is not an automatic alternative completion.

Additionally, the actual statistical source still needed explicit coordinate
polynomial identities and degree bounds, preserved through the source image
and boson symmetric quotient. For paired Weyl factors these must use real
and imaginary parameters: the proved two-variable interpolation lemma does
not make z and conj(z) independent actual group variables. Finite source
bases/matrix entries must be constructed before a computational rank test
can classify all contents.

This reached the frozen plan's actual special-unitary generating-family
stop. No missing premise was added to claim fixed-input success. The complete
SM matrix connection and q/l support classification were open here; this was
not an impossibility result. The generic matrix connection, interpolation
and actual Weyl controls are retained as a verified checkpoint.

## Subsequent prerequisite discharge

The [SU(3) child result](../su3-plane-generation/results.md) subsequently
proves the actual plane-family algebraic generation and three-plane
factorization without an external premise. The earlier stop above records
this checkpoint's boundary; generation is discharged in the child. The later
[statistical](../sm-statistical-finite-kernel/results.md) and
[compact](../sm-compact-kernel-completion/results.md) results discharge the
remaining source, sampling and compact-group obligations and complete the
existing q/l finite-rank classifier.
