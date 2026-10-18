# Hermitian Action Recalculation Result

The [plan](hermitian-plan.md) is complete at its bounded endpoint. Literal H.c.
now replaces the independent barred data used in the earlier projection.
The selected holomorphic degree-six coefficient is unchanged in the exact
finite diagnostic. This does not establish adoption of our conventions by
the paper or certify an error in its printed coefficient.

## Formal action and scalar elimination

[DevMohapatraHermitian.lean](../../../Physics/StandardModel/Operators/DevMohapatraHermitian.lean)
uses a ring with a complex algebra and compatible star. Star conjugates
complex coefficients and reverses multiplication. For each color let

```
V = a U chiBar + b chi D,  chiBar = star chi
L_scalar = m chi chiBar + V + star V
J = a U + conjugate(b) star D
K = b D + conjugate(a) star U = star J.
```

The scalar mass m is real and nonzero; M,a,b may be complex. The Majorana
part is -M N0 N1 plus its literal star. In particular its conjugate is
-conjugate(M) star(N1) star(N0), with reversed spin order. Reordering odd
barred components makes this +conjugate(M) Nbar0 Nbar1. This sign is important:
the independently supplied conjugate mass in the previous completion must
be identified as Mc = -conjugate(M) in this field convention.

The scalar solutions are chi = -J/m and chiBar = -K/m. Their conjugacy,
Hermiticity of the original and effective actions, and equality of the
on-shell scalar action with -JK/m are proved. The expanded effective term is

```
-(a b/m) U D
-(a conjugate(a)/m) U star U
-(conjugate(b) b/m) star D D
-(conjugate(b) conjugate(a)/m) star D star U.
```

No mixed channel is discarded. The aggregate action counts the scalar mass
once, and `action_scalar_on_shell` eliminates all three scalar components.
`effective_projection` proves the scalar-level holomorphic projection when
the images of star U and star D vanish. No zero heavy-field image is assumed
in this theorem.

These are general Lean identities for the supplied star-algebra interface,
not a construction of a physical ExteriorAlgebra star instance. mathlib's
Clifford conjugation fixes scalar coefficients and does not supply the
required complex-conjugating instance automatically.

## Full finite Grassmann recalculation

[check-hermitian-action.py](../../../tools/dev-mohapatra/check-hermitian-action.py)
represents all 18 unbarred and 18 barred external components and four heavy
components N0,N1,Nbar0,Nbar1. H.c. reverses monomials and swaps barred and
unbarred generators. The tested coefficients are exact real rationals;
complex phases are covered by the generic scalar Lean identities, not this
finite heavy-field test.

After exact scalar elimination the script differentiates the resulting
Grassmann action with **left** derivatives in each heavy component. It solves
the coupled stationary equations through external degree five by iteration,
checks a further iteration changes nothing at that truncation, and evaluates
the original action including H.c. at the scalar/heavy solutions through
external degree six. Both original and eliminated evaluations agree. The
stationary residual through degree five is zero, and heavy solutions and
effective action respect H.c.

The output consists of the mixed degree-four term
-(b squared/m) sum star(D) D and, at degree six, the previously obtained
(g squared/M) J0 J1 plus its H.c., where g = a b/m. There are 48 degree-four
monomials and 180 degree-six monomials. Projection killing barred external
generators kills the computed barred heavy solution and yields exactly the
previous chiral solution and its 90 degree-six monomials.

The two cases are (m,M,a,b) = (2,3,1,1) and (-5,7,2,-6), covering a scalar
mass sign change and the doubled down-flavor coupling. They are checks of
these two full polynomial instances, not an exhaustive parameter proof.
At this order the mixed U star(U) term starts at degree eight because each
heavy solution starts at degree three. Its degree-two correction to the
heavy kernel first changes the solution at degree five and the action at
degree eight. Discarding these higher degrees therefore does not affect the
computed degree-six coefficient. No all-degree heavy solution is claimed.

## Assessment and remaining boundary

The literal H.c. completion supplies additional consistency evidence for
the earlier coefficient. With the existing inverse-C dictionary its sign
and magnitude comparison remain as in the [literature evaluation](literature-evaluation-results.md):
conditional -8 pi squared, or -32 pi squared with the doubled ordered-flavor
vertex. The related sources do not prove that the target adopted that
normalization; this recalculation does not fix that provenance gap.

Fully formalizing the heavy-field part would still require a compatible
complex anti-involution on the physical Grassmann carrier and a proof of
its graded stationary/elimination bridge. Here it is a reproducible bounded
calculation, clearly separated from the Lean scalar theorem. No physical
amplitude, loop matching, rates, author notification or integration is claimed.

The subsequently authorized [all-degree Lean phase](heavy-elimination-results.md)
discharges the concrete exterior anti-involution and heavy stationary/action
bridge left open above. The earlier diagnostic remains independent bounded
evidence; target-source convention adoption remains conditional.
