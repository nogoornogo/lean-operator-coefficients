# All-Degree Heavy-Fermion Elimination Result

The [all-degree plan](heavy-elimination-plan.md) is complete for the declared
one-N, selected u,d,s, derivative-free Hermitian action. The earlier rational
Grassmann calculation is now supplemented by parameter-uniform Lean proofs
of the exact stationary solution, uniqueness, substitution and eliminated
action. **No external-degree truncation is used.** Adoption of this action's
normalization by the literature remains conditional.

## Statement and explicit inputs

The external carrier is the exterior algebra over 36 complex coordinate
generators: the 18 u,d,s color/spin components and their 18 conjugates. A
second exterior algebra adds four heavy coordinates N0,N1,Nbar0,Nbar1. Field
conjugation complex-conjugates coefficients, exchanges barred/unbarred
coordinates and reverses multiplication. This anti-involution is constructed
and proved, rather than supplied as an uninstantiated interface.

For the original scalar elimination assume m is real and nonzero. For heavy
elimination assume M is nonzero. M,a,b may be arbitrary complex numbers;
there is no reality or nonzero assumption on either coupling. The action
uses the earlier Majorana half and vertex normalization, counts the scalar
quadratic term once, and includes literal H.c. of the mass and vertices.
No momentum-dependent kinetic inversion is asserted.

## Exact inverse and coupled stationary solution

After scalar elimination set c = a conjugate(a)/m, g = a b/m and
C_rt = sum_color u_r ubar_t. The four left stationary equations take the
form n - T n = source. In N0,N1,Nbar0,Nbar1 order,

```
T = [[0, 0, -c C01/M,       c C00/M],
     [0, 0, -c C11/M,       c C10/M],
     [-c C10/conj(M), c C00/conj(M), 0, 0],
     [-c C11/conj(M), c C01/conj(M), 0, 0]]

source = [-g J0/M, -g J1/M,
          conjugate(a) conjugate(b) K0/(m conjugate(M)),
          conjugate(a) conjugate(b) K1/(m conjugate(M))].
```

J and K are the unbarred and barred cubic color currents. Every entry of T
has exterior degree two. A general theorem proves that a matrix with entries
of degree d has nth-power entries of degree d n; a finite spanning family
forces that exterior power to vanish once d n exceeds its size. Here 38 > 36,
so **T to the nineteenth power is zero**, proved for all parameters.

Consequently the exact solution is

```
n_exact = (1 + T + ... + T^18) source.
```

Both inverse identities, every stationary equation and uniqueness are
proved. The bound nineteen is sufficient; no sharpness claim is made.
Neither invertibility nor stationarity is imported from Python.

## Action, differentiation and genuine substitution

[HeavyAction](../../../Physics/StandardModel/Operators/DevMohapatraHeavyAction.lean)
uses mathlib Clifford contraction at zero quadratic form as the left
Grassmann derivative. The graded Leibniz rule is proved in the local shared
[derivative adapter](../../../Math/LinearAlgebra/ExteriorLeftDerivative.lean).
Differentiating the universal quadratic action and then substituting any odd
heavy configuration gives exactly the four displayed residuals. This is an
action-to-equation bridge, not a definition that calls a chosen residual a
derivative.

The exact solution is proved odd under grade involution. Shared lemmas prove
anticommutation and square zero for arbitrary odd exterior polynomials,
including inhomogeneous ones. These square-zero identities admit an actual
ExteriorAlgebra algebra homomorphism replacing the heavy generators by their
solutions and preserving external generators. All four contracted action
terms vanish after that substitution. A uniqueness theorem applies to the
actual differentiated action.

The heavy quadratic Euler identity then proves the exact on-shell action
is one half of the linear source term at n_exact plus the heavy-independent
term. Mixed channels and all higher Grassmann corrections are retained.
[HeavyHermitian](../../../Physics/StandardModel/Operators/DevMohapatraHeavyHermitian.lean)
proves that this universal quadratic action is precisely the literal H.c.
action after the earlier exact scalar elimination. `full_eliminated_action`
connects the original scalar action to the all-degree result.

[HeavyConjugacy](../../../Physics/StandardModel/Operators/DevMohapatraHeavyConjugacy.lean)
proves covariance of all four residuals under conjugation. Uniqueness then
proves that the barred heavy solutions are the adjoints of the unbarred
solutions. The full exterior substitution commutes with H.c.; the exact
eliminated action is Hermitian. No extra zero-barred-heavy or conjugacy
premise is assumed.

## Previous coefficient recovered

[HeavyProjection](../../../Physics/StandardModel/Operators/DevMohapatraHeavyProjection.lean)
constructs the holomorphic projection killing all barred external
generators. It kills the mixed kernel, so the exact projected solution is
the earlier chiral solution, and the barred heavy solution vanishes as a
proved consequence. The heavy-independent mixed term also projects to zero.

`holomorphic_full_action` proves that projecting the original H.c. action
after exact scalar and heavy elimination gives precisely the previous
`generated` polynomial. Thus the earlier coefficient
(a b) squared/(2 m squared M), and its inverse-C signed transport, survive
full all-degree elimination. The conditional -8 pi squared or -32 pi squared
comparison in the [literature evaluation](literature-evaluation-results.md)
is unchanged. This does not prove the target adopted our action dictionary.

## Reuse in other verifications

The common mathematics is independent of the paper and sector:

| Shared module | Reusable result | Model-specific input still needed |
| --- | --- | --- |
| [NilpotentQuadraticElimination](../../../Math/LinearAlgebra/NilpotentQuadraticElimination.lean) | Finite exact inverse, unique source solution and algebra-valued quadratic on-shell identities | Action's bilinear form, source and first-variation factorization |
| [ExteriorNilpotentKernel](../../../Math/LinearAlgebra/ExteriorNilpotentKernel.lean) | Proved nilpotence and exact inverse for arbitrary finite heavy matrix size | Finite external spanning family and entry degree |
| [ExteriorOdd](../../../Math/LinearAlgebra/ExteriorOdd.lean) | Odd anticommutation, square zero, even centrality | Odd/even identification of candidate fields |
| [ExteriorLeftDerivative](../../../Math/LinearAlgebra/ExteriorLeftDerivative.lean) | Actual left derivative and graded Leibniz rule | Heavy-coordinate duals and action polynomial |
| [ExteriorHermitianConjugation](../../../Math/LinearAlgebra/ExteriorHermitianConjugation.lean) | Complex anti-involution and local compatible star structures | Involutive semilinear field dictionary |

Other derivative-free tree-level quadratic heavy-field problems can reuse
these modules. They are not tied to Delta B = 2 or four heavy components.
The concrete mass/vertex convention, kernel and action connection must still
be checked for each model. A singular constant mass kernel, nonquadratic
heavy interactions, infinite field carrier or momentum-dependent kinetic
operator is not automatically handled by this finite-inverse argument.
This is Grassmann-coordinate differentiation, not spacetime derivative,
EOM/IBP, loop, amplitude or rate formalization.

See [verification](verification.md) and [library provenance](references.md).
