# Paired Adjoint Candidate: Compensation Works, Standard Color Fails

## Explicit Candidate Choices

Continue the existing signed color/singlet exchange w=(3 6), but add two adjoint
scalar copies and an external copy exchange. On matrix pairs use

```text
U_scalar(X,Y) = (Ad_w(Y), Ad_w(X)).
V = (v, Ad_w(v)),   v = diag(1,1,1,1,1,-5).
```

The extra scalar copy and its external exchange are explicit candidate choices,
not conclusions from the original project conditions. This tests whether the
[earlier failed vacuum equation](weyl-candidate-result.md) can be compensated.
The intended color embedding still acts on the first three coordinates, with
weak coordinates fourth/fifth and the extra singlet sixth.

## Verified Gates

[PairedAdjointCandidate](../../../GUT/SU6/SelectionRules/Models/PairedAdjointCandidate.lean)
proves fourth-power identity of the scalar transformation on every matrix pair,
using the actual SU(6) relation w^4=1 and conjugation composition. Thus a
cyclic order-four generator relation is consistent; exact order is not asserted.
It also proves `U_scalar(V)=V`. The vacuum failure of the single-adjoint
candidate has genuinely been repaired at the matrix-pair level.

Now take a signed exchange of the first and third coordinates. The module
constructs its actual determinant-one unitary SU(6) matrix `colorElement`,
with identity rows outside the first three coordinates. It is the signed
color-block transformation, leaving the weak and singlet coordinates alone.
It fixes v but fails to fix Ad_w(v): the exceptional -5 eigenvalue in the
latter sits on the third color coordinate, and the color exchange moves it
to the first coordinate. The nonzero difference is checked exactly at the
first diagonal entry. Consequently this transformation does not preserve V.

The candidate therefore cannot keep the entire specified standard color
block as an unbroken gauge symmetry. This is a vacuum/gauge obstruction before
any fermion mass, light spectrum or Lorentz/BNV computation. Scalar residual
fixedness alone would have missed it.

## Scope And Search Outcome

This is a concrete compensated scalar candidate, rejected for the specified
standard color embedding. It is not a protecting `AutomorphismCovariantModel.Model`
inhabitant. The code does not instantiate continuous-unitary scalar/matter
representations, the full cyclic residual homomorphism, its SM target or a
physical operator carrier. Those later constructions are unnecessary for this
rejection because an intended unbroken color transformation already fails
vacuum fixedness.

No exclusion of all color embeddings, all paired scalars, all compensated
residual actions or all SU(6) protection is inferred. In particular, merely
choosing a different vacuum or embedding needs a fresh check of its SM field
and gauge dictionary. No UV weight-support/radical identification is assumed.

The bounded [plan](paired-adjoint-plan.md) is complete after verification.
The next search should not repeatedly reuse this color/singlet swap with the
same standard vacuum embedding: even scalar-copy compensation leaves a
specified color generator broken. A different scalar/embedding/action route
is needed for an actual candidate that passes both gates. No solution is
claimed; general classification, physical rates and master integration remain
outside this endpoint.

## Verification

The persistent [strict audit](../../../GUT/SU6/SelectionRules/Audit/AuditPairedAdjointCandidate.lean)
covers nine declarations and allows only `propext`, `Classical.choice`,
`Quot.sound`.

- `lake build GUT.SU6.SelectionRules.Audit.AuditPairedAdjointCandidate`:
  passed, 3,216 jobs; nine strict transitive checks.
- `lake build`: passed, 6,583 jobs on final source state, no warnings.
- `node tools/layout/check-layout.mjs`: 1,256 modules passed.
- `node tools/docs/check-links.mjs`: 518 Markdown files, 3,381 local inline
  links, 85 heading fragments, zero errors.
- `git diff --check`: passed; scalar/embedding scope and final source reviewed.

 Development inverse-notation, associativity and matrix-entry
simplification errors were corrected without changing the hypotheses,
heartbeat limits, pins or audit allowances.
