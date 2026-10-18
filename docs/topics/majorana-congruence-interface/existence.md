# Takagi existence extension

## Statement

For every finite index type I and complex symmetric matrix M, without a
nondegeneracy or distinct-eigenvalue assumption:

```
M.IsSymm ↔ ∃ m : I → ℝ, (∀ i, 0 ≤ m i) ∧
  ∃ U : Matrix.unitaryGroup I ℂ,
    U.val.transpose * M * U.val = Matrix.diagonal (fun i => (m i : ℂ)).
```

This is proved by `TakagiExistence.symmetric_iff_exists_nonnegative_diagonal`,
not supplied as a literature or model premise. All finite sizes, including
empty, zero and degenerate cases, are covered. No infinite-dimensional Takagi
statement is asserted.

## Proof structure

- [AntilinearSpectral](../../../Math/LinearAlgebra/AntilinearSpectral.lean)
  treats an additive conjugate-linear T on any finite-dimensional complex
  inner-product space satisfying `inner (T x) y = inner (T y) x`.
  Restricting to real scalars makes T a symmetric real linear map. The proved
  Mathlib real spectral theorem supplies a nonzero eigenvector; normalization
  supplies a unit eigenvector with real eigenvalue.
- Complex orthogonal-complement induction constructs a complete complex
  orthonormal basis of T-eigenvectors. The complement is invariant by the
  displayed symmetry. Its complex dimension drops by exactly one. This avoids
  selecting vectors independently inside repeated-eigenvalue spaces. The
  zero-dimensional base is explicit.
- [TakagiExistence](../../../Math/LinearAlgebra/TakagiExistence.lean)
  applies this to `T x = conj (M.mulVec x)`. Matrix symmetry proves the required
  inner-product symmetry. The columns of the resulting basis form a verified
  unitary matrix, and the eigenvector equations give real diagonal congruence.
- The already proved diagonal phase normalization makes every coefficient
  nonnegative. Inverse congruence also proves that symmetry is necessary.

Finite-dimensional compactness/spectral theory is used through proved Lean
theorems, not numerical eigensolvers or external assumptions. No dependencies,
pins or resource limits are changed. The diagonal values are not sorted; a
separate identification with Mathlib's sorted singular-value sequence or a
coefficient-only uniqueness theorem is not part of this existence endpoint.

## Physical interface

[FlavorMajoranaCertificate](../../../Physics/FieldTheory/Mass/FlavorMajoranaCertificate.lean)
now provides `ofSymmetric M hM : Input I`, with matrix exactly M and a proved
normalization certificate. `fromDiagonal_surjective` proves that the earlier
parametrization covers all symmetric matrices. Thus the existing stabilizer
classification, exact fixed-target basis freedom, residual Hom equivalence
and nonzero-existence criterion apply via `ofSymmetric`, without an external
Takagi premise. Consumer modules in the Hom transport remain unrestricted in
dimension; only the matrix carrying the Majorana form is finite.

The existence choice is noncomputable and not claimed continuous in M.
Simultaneous Yukawa orbit classification, mass fitting, physical matching and
topological group equivalences remain outside scope.

## Verification

- Focused build of `Math.LinearAlgebra.Audit.AuditTakagiExistence` and
  `Physics.FieldTheory.Mass.Audit.AuditFlavorMajoranaCertificate` passed
  (3700 jobs).
- Persistent strict transitive audits: 12 Takagi declarations and 11 physical
  interface declarations. Only `propext`, `Classical.choice`, `Quot.sound`
  allowed; no `sorry`, custom axiom or external existence premise.
- Regression proofs cover a nondiagonal singular symmetric matrix and exclude
  a nonsymmetric matrix. Empty and zero dimensions are included by the general
  proof, not by a nonempty side condition.
- Full `lake build` passed (6067 jobs), with no new-source warnings; existing
  dependency warnings replayed. Intermediate elaboration failures were fixed,
  not accepted as verification.
- Layout passed (1014 modules). Links passed (358 Markdown files, 2276 local
  links, 34 fragments, zero errors). Final source review and `git diff --check`
  passed. No resource-limit increase, dependency change or audit exception.
- These are the extension's pre-merge checks. Master integration at `checkpoint 01`
  and merged-state checks are recorded in the [topic overview](README.md#integration).
  No remote push was made; the proof branch is retained.
  Unrelated user documentation changes remain excluded. Existing operator
  normalization scripts were not rerun because their definitions are unchanged.
