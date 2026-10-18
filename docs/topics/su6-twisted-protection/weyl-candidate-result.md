# Concrete Weyl-Exchange Candidate: Vacuum-Gate Rejection

## Candidate And Why Test It

Take the existing determinant-one signed Weyl representative w exchanging the
third standard color coordinate and the sixth extra singlet coordinate. This
is a concrete inner transformation outside the usual fixed-sixth-coordinate
standard branch, so it tests an outstanding route rather than another
unspecified automorphism. Use conjugation by w on an adjoint scalar.

Specify the scalar vacuum as `diag(1,1,1,1,1,-5)`. This is an explicit additional
candidate input: a trace-zero 5+1 adjoint split, not a condition derived from
the original project hypotheses. No external scalar action is included to
compensate the conjugation. On fermions the proposed pure inner action is
rho(w); no choice of matter is needed to test this scalar gate first.

## Exact Lean Results

[WeylExchangeCandidate](../../../GUT/SU6/SelectionRules/Models/WeylExchangeCandidate.lean)
reuses the actual SU(6) element from
[WeylMatrix](../../../GUT/SU6/Characters/WeylMatrix.lean) and proves:

- The chosen vacuum has trace zero.
- `w^4 = 1`, both as an actual matrix and in SU(6). Thus the generator has
  the relation needed for a cyclic order-four candidate; exact order and a
  fully instantiated cyclic-group action are not claimed by this statement.
- For any diagonal vacuum with coordinates d, conjugation by w fixes it
  exactly when `d(3) = d(6)` (one-based coordinate names).
- Every nondegenerate 5+1 diagonal split `diag(a,a,a,a,a,b)` with a≠b fails
  that fixed-vacuum equation.
- In particular, conjugating the chosen vacuum gives
  `diag(1,1,-5,1,1,1)`, not the chosen vacuum. The sixth diagonal entry
  changes from -5 to 1, providing the exact witness of inequality.

The sign correcting the transposition's determinant does not alter its action
on diagonal vacua. The fourth-power proof factors through the diagonal square
of the signed representative instead of expanding large matrix products.

## Interpretation And Stop Gate

This specific pure-inner scalar transformation cannot be an unbroken residual
symmetry of the specified vacuum. It fails the required `vev_residual` condition
before any mass-radical, target or Lorentz/BNV-Hom calculation. Rejecting it here
avoids pretending those later inputs are already available. This is a concrete
failed candidate, not a full `AutomorphismCovariantModel.Model` construction.

For a single diagonal adjoint vacuum, the precise way to pass this generator's
vacuum gate is to equate the exchanged eigenvalues. That changes the proposed
breaking pattern and must be treated as a different candidate input. Fixedness
would also put this pure gauge transformation in that vacuum's stabilizer;
pure gauge factors do not create a new selection rule on local gauge-invariant
coefficients, as [the earlier comparison](remaining-result.md) proves when the
local gauge carrier includes that element. No exact stabilizer classification
or final-stage gauge embedding is inferred here.

This rejection does not exclude other scalar representations, other vacua,
additional external scalar actions, compensated residual actions, or all
protecting SU(6) models. A scalar action compensating the exchange would need
its own genuine group law and an actual fixed vacuum; it is not supplied in
this candidate. No quantum stability or proton lifetime is asserted.

## Verification

The [frozen plan](weyl-candidate-plan.md) and
[strict transitive audit](../../../GUT/SU6/SelectionRules/Audit/AuditWeylExchangeCandidate.lean)
cover six declarations. Only `propext`, `Classical.choice`, `Quot.sound` are
permitted; dependency pins and audit allowances are unchanged.

- `lake build GUT.SU6.SelectionRules.Audit.AuditWeylExchangeCandidate`:
  passed, 3,211 jobs; six strict transitive checks.
- `lake build`: passed, 6,577 jobs on final source state, no warnings.
- `node tools/layout/check-layout.mjs`: 1,250 modules passed.
- `node tools/docs/check-links.mjs`: 514 files, 3,367 local inline links,
  85 heading fragments, zero errors.
- `git diff --check`: passed; explicit candidate choices and hypotheses reviewed.


Development matrix-inverse coercion, permutation simplification and an
elaboration failure were corrected without adding proof assumptions or
increasing heartbeat limits. No master merge is authorized.
