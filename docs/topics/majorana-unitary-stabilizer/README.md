# Full Unitary Stabilizer Of A Specified Diagonal Majorana Form

- ID: `majorana-unitary-stabilizer`
- Status: completed
- Checkpoint detail: completed; merged into master at `checkpoint 01`.
- Working branch: `proof/majorana-unitary-stabilizer`
- Integration target: master; merged on user instruction, no remote push.
- Result type: bounded algebraic proof package.

## Frozen Endpoint

Given a finite index set and specified complex diagonal coefficients `c`,
classify the entire unitary subgroup preserving the complex bilinear Majorana
form, not just independent phases. The exact matrix equation is
`U.transpose * diagonal c * U = diagonal c`; transpose is deliberately not
conjugate transpose. Preserve empty, zero, nondegenerate and degenerate cases.

1. Prove an equivalent entry criterion and no mixing across unequal absolute
   values. Construct an actual subgroup and connect the bilinear-form action.
2. For supplied nonnegative real diagonal coefficients, classify zero blocks
   as unitary and positive equal-value blocks as real orthogonal, with an
   explicit group equivalence and inverse.
3. For arbitrary complex coefficients, construct phase normalization and
   transport the stabilizer. Do not silently replace complex inputs by real
   inputs or confuse equal coefficients with equal absolute values.
4. Transport residual Hom/nonzero conditions, audit, build and commit.

No Takagi theorem for arbitrary nondiagonal matrices, simultaneous Yukawa orbit
classification, numerical fitting, dynamics or physical flavor prediction is
required. Stop on a new foundational prerequisite or an unexpected false
classification; keep partial theorems and unfinished obligations explicit.

## Existing Sources

- [Independent-phase classification](../../../Physics/FieldTheory/Mass/FlavorMajoranaDiagonal.lean)
- [General specified coupling stabilizers](../../../Physics/FieldTheory/Yukawa/FlavorStabilizer.lean)
- [Diagonal commutants](../../../Math/LinearAlgebra/DiagonalCentralizer.lean)
- [Algebraic Hom transport](../../../Math/RepresentationTheory/Decomposition/SurjectiveHomTransport.lean)

## Verification And Remaining Work

Master merge `checkpoint 02` was performed in a clean separate worktree to exclude
unrelated user documentation changes. The new branch starts from the subsequent
integration-record commit `checkpoint 03`. Baseline full build passed (6054 jobs).
Those are inherited results, not verification of new sources. The integration
record itself was documentation-only and did not rerun Lean.

The [matrix criterion](../../../Math/LinearAlgebra/UnitaryDiagonalCongruence.lean)
now constructs the full unitary subgroup, proves equivalence with preservation
of the actual complex bilinear form, and derives the exact entry condition
`c i * U i j = star (U i j) * c j`. Unequal squared absolute values force
zero mixed entries. For nonnegative real coefficients, preservation is
equivalent to no mixing between different masses and real entries on every
nonzero row. The all-zero form has the full unitary group.

`constantEquiv` proves an explicit group equivalence of the stabilizer of a
constant nonzero complex diagonal form with `Matrix.orthogonalGroup I ℝ`.
It uses complexification of real matrices and an inverse recovered from real
parts; no external diagonalization premise is used. All index sets may be empty.

The [persistent strict audit](../../../Math/LinearAlgebra/Audit/AuditUnitaryDiagonalCongruence.lean)
passes 10 transitive checks, allowing only `propext`, `Classical.choice` and
`Quot.sound`. Focused build passed (3073 jobs), without new-source warnings.
Earlier elaboration failures were corrected, not accepted as proof evidence.

First milestone full `lake build` passed (6056 jobs). Layout passed (1003
modules); local links passed (355 documents, 2256 links, 34 fragments); diff
checks passed. Existing dependency warnings replayed. Pins, dependencies,
resource limits and audit exceptions are unchanged. No operator coefficient
normalization script was rerun, since the covered operator definitions are
unchanged. Unrelated user documentation changes remain excluded from commits.

The continuation has now proved all group-output stages. See
[complete result and boundaries](results.md) for the full product equivalence,
phase normalization without additional input premises, physical-form adapter,
residual Hom/nonzero transport and regression controls. Final verification is
recorded below; no master integration of this new topic is authorized.

Final continuation verification (stage 01):

- Focused Math/Physics audits passed: 3777 jobs; 32 and 60 strict transitive
  checks respectively, only `propext`, `Classical.choice`, `Quot.sound`.
- Full `lake build` passed: 6060 jobs. No new-source warnings; existing
  dependency warnings replayed. All intermediate failures were corrected.
- Layout passed: 1007 modules. Local links passed: 356 documents, 2265 links,
  34 fragments, zero errors. `git diff --check` passed.
- No pins, dependencies, custom axioms, allowlist exceptions or resource limits
  changed. Unrelated user changes are excluded from this topic's commit.
- All four frozen endpoint stages are proved. Nondiagonal Takagi, simultaneous
  Yukawa classification and topological group equivalences remain outside scope.
- Subsequent user-authorized integration: master merge `checkpoint 01` includes
  topic commit `checkpoint 04`. The merged proof sources passed full `lake build`
  again (6060 jobs); unrelated user documentation changes were excluded.
  No remote push or branch deletion was performed.
