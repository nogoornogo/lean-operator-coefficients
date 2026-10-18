# Classification Of Diagonal Vacua Within The Weyl Family

## Exact Classification

[DiagonalWeylStabilizer](../../../Math/LinearAlgebra/Matrix/DiagonalWeylStabilizer.lean)
works on any finite index set with complex diagonal coordinates d. For any
permutation sigma and any unit-modulus diagonal phases u, define

```text
W = diagonal(u) * permutationMatrix(sigma).
W diagonal(d) W* = diagonal(d composed with sigma).
W diagonal(d) W* = diagonal(d) iff for every i, d(sigma(i)) = d(i).
```

Here W* is the conjugate transpose. The convention is mathlib's row-permutation
matrix convention. The diagonal phases cancel, so determinant-correcting signs
and other unit phases do not affect vacuum preservation.

The module constructs the subgroup `preserving d` of exactly those permutations
preserving d. Thus the complete test within this family is preservation of each
eigenvalue fiber, not a check of just the previously chosen transposition.
The subgroup is defined and its multiplication/inverse closure proved; an
isomorphism to a product of symmetric groups is not constructed or claimed.

For a singleton split, with d(j)=b and d(i)=a for i different from j and a≠b,
this subgroup is precisely the permutations fixing j. When a=b all permutations
preserve d, as also follows directly from the general condition.

## SU(6) Specialization

[DiagonalWeylClassification](../../../GUT/SU6/SelectionRules/Models/DiagonalWeylClassification.lean)
accepts an actual SU(6) element w together with its equality to a phase/permutation
matrix. Its group inverse is the conjugate transpose, giving the actual SU(6)
conjugation criterion. For the nondegenerate 5+1 split, preservation is equivalent
to fixing the sixth coordinate; the other five may be permuted subject to the
supplied representative data.

This proves the criterion for every supplied representative of the indicated
form. It does not construct a determinant-one representative for every
permutation, or prove that all SU(6) automorphisms or all stabilizer elements
have that form. General unitary mixing within a degenerate eigenspace is not
classified by a permutation-family theorem. The diagonal need not be traceless
for the Math theorem; trace-zero adjoint vacua are included as a special case.

The earlier [concrete `(3 6)` rejection](weyl-candidate-result.md) is the special
case exchanging unequal eigenvalues. Its checked proofs remain unchanged.
This generalizes the vacuum rejection, not the proton-protection conclusion.
Pure gauge factors are still handled separately by the local-coinvariant tests;
no external-action, scalar-family, mass-radical or BNV-support premise is inferred.

## Verification

The [frozen plan](weyl-classification-plan.md) is implemented. Persistent strict
transitive audits cover six Math declarations and two SU(6) declarations, with
only `propext`, `Classical.choice`, `Quot.sound` permitted. Final focused/full
builds passed: focused audit build 3,216 jobs; full `lake build` 6,581 jobs,
with no warnings on final source state. Layout checked 1,254 modules; links
checked 516 Markdown files with zero errors; `git diff --check` passed.
Commands: `lake build Math.LinearAlgebra.Matrix.Audit.AuditDiagonalWeylStabilizer
GUT.SU6.SelectionRules.Audit.AuditDiagonalWeylClassification`, `lake build`,
`node tools/layout/check-layout.mjs`, `node tools/docs/check-links.mjs`.
Development errors in inverse-permutation notation, pointwise star reduction
and section-variable placement were corrected; no global heartbeat change,
dependency change or audit exception. No master merge is authorized.
