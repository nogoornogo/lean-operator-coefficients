# Frozen Proof Plan

## Statement And Interfaces

Let H be a finite group, I and J finite coordinate types, and a and b complex
linear representations on I -> C and J -> C. For every s : I -> C prove
`Function.Surjective (Math.PolynomialCovariantEvaluation.evaluation a b s)`.
Use the existing definitions of covariants, stabilizer and evaluation in
[the source](../../../Math/RepresentationTheory/PolynomialCovariantEvaluation.lean).
The covariant law is p(a(g)x) = b(g)p(x); coordinate polynomials are holomorphic.
The polynomial domain allows all degrees, with each witness an actual finite
polynomial. No formal series or completion is introduced.

The coefficient consumer uses the contragredient action
(g f)(q) = f(g^{-1}q), so stabilizer-fixed dual vectors are exactly stabilizer
invariant functionals. Transport finite-dimensional spaces through chosen
bases without changing the original quotient or its statistics relations.
Do not infer finite dimensionality of every existing Q_c automatically.

## Primary Construction

1. For w fixed by H_s, define f(hs) = hw on the finite orbit O = Hs.
   Prove independence of representatives using the actual stabilizer.
2. For each t in O and u != t choose a separating coordinate i and use
   (X_i - u_i)/(t_i - u_i). Multiply over u to obtain a delta polynomial
   equal to one at t and zero at every other orbit point.
3. Interpolate the J coordinates of f to obtain P with P(t) = f(t).
4. Form R(x) = (1/|H|) sum_g b(g^{-1}) P(a(g)x), proving that linear
   substitutions and finite sums remain coordinate polynomials.
5. Prove R(a(h)x) = b(h)R(x) by reindexing, and R(s) = w.

This handles the singleton orbit, zero value, nonfaithful actions and empty
coordinate types. Division by |H| is justified over C. No extension to
positive characteristic is part of the endpoint.

## Bounded Feasibility Pass And Stop

Inspect at most two routes, once each:

- A: explicit coordinate separation/product interpolation plus polynomial
  substitution and a finite Reynolds sum, using existing library primitives.
- B: reuse an existing finite-set interpolation/surjective restriction API,
  then use the same finite averaging construction.

Helper lemmas for separation, orbit representatives, substitution, finite sums
and dual-coordinate transport are within scope. If both routes require a new
theorem-level foundation outside these interfaces, record the missing input
and stop for a scope decision. Do not replace it with an assumed premise.
No wall-clock or memory cap has been supplied; this does not authorize
unbounded computation or a new foundational project.

## Validation And Boundaries

Persist strict axiom checks for interpolation, covariance, surjectivity and
the coefficient consumer; allow no custom axioms or new audit exceptions.
Use focused Lean builds before a serialized full build, plus layout, links
and diff checks. Include meaningful controls for zero/singleton orbits and
a nontrivial finite action; a nonabelian example is optional, since H is
arbitrary in the theorem. Do not start an S3 classification.

The construction suggests degree at most |O|-1, preserved by averaging.
This is an optional corollary only if supported directly by existing degree
APIs; it is not a required acceptance gate or a global EFT dimension cutoff.
No claim of priority, general continuous-group saturation, or physical
generation follows. Planning approval does not authorize implementation or merge.

## Authorized Degree-Bound Extension

The same branch now extends the proved endpoint with a total-degree bound.
For finite H and finite coordinate source/target, every stabilizer-fixed vector
must be attained by a covariant p with each coordinate's `totalDegree` at most
`(Finset.univ.image (fun g : H => a g s)).card - 1`. Derive the uniform bound
`Fintype.card H - 1` and transport the bounded witness to the existing residual
coefficient consumer. Natural subtraction covers singleton orbits; an orbit
is never empty. This is a spurion polynomial degree, not an EFT mass dimension.

Keep the earlier hypotheses and definitions. Prove bounded separation and
interpolation, then nonincrease of degree under the existing linear
substitutions, target linear maps and Reynolds average. Existing degree APIs
and helper lemmas for these operations are allowed. No new invariant theory,
optimality classification, general-group theorem or derivative topic is opened.
Stop if this requires a separate foundation outside polynomial-degree helpers;
do not assume the bound. Add strict audits and zero-orbit/nontrivial-action
controls, focused builds, layout and documentation checks, and a serialized
full build before recording completion and committing. Merge still requires
separate direction. No additional resource cap or dependency change is authorized.
