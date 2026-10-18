# Majorana congruence certificates and basis freedom

- ID: `majorana-congruence-interface`
- Status: completed
- Checkpoint detail: completed, including Takagi existence; merged into master at `checkpoint 01`.
- Working branch: `proof/majorana-congruence-interface`.
- Integration target: master; user authorized merging at stage 01. No push authorized.

## Frozen endpoint

The certificate endpoint below was completed at `checkpoint 02`. On stage 01 the
user additionally requested existence for every finite complex symmetric matrix.
The extension must prove `exists m, (∀ i, 0 ≤ m i) ∧ exists P : unitaryGroup I ℂ,
P.transpose * M * P = diagonal (fun i => (m i : ℂ))` from `M.IsSymm` alone,
including zero, empty and repeated-value cases, and supply the physical Input.
The selected route is the real spectral theorem for the symmetric antilinear
operator associated to M, followed by complex orthogonal-complement induction
and diagonal phase normalization. Existing proved Mathlib spectral results
are allowed; no diagonalization premise, distinctness assumption or axiom may
replace the goal. Simultaneous Yukawa classification remains excluded.

For a specified finite complex symmetric matrix M, accept a unitary congruence
certificate `P.transpose * M * P = diagonal c`. Prove an explicit equivalence
of the actual stabilizer with the already classified diagonal stabilizer and
its U/O product, and transport residual Hom and nonzero existence.

For a fixed target diagonal form and a fixed certificate P, prove that all
certificates are uniquely `P * S` for S in the target stabilizer. This is a
bijection of types, not a group structure on the set of certificates.

The transport lemmas hold for arbitrary matrices without symmetry; symmetry is
required by the Majorana interpretation and the Takagi existence theorem.
At the original `checkpoint 02` milestone, diagonalization was supplied as a
certificate. The `checkpoint 03` extension proves its existence from symmetry alone;
see [existence proof and endpoint](existence.md). Simultaneous diagonalization,
topological equivalences and physical matching remain excluded. No new
dependencies, axioms or resource-limit increases are allowed.

The extension is now proved and verified: arbitrary finite symmetric matrices
yield a physical `Input` through `ofSymmetric`, with no supplied diagonalization
premise. Full build passed (6067 jobs); strict audits passed (12 Takagi and 11
physical declarations). Layout/link/diff checks passed. Master integration is
complete; its merged-state verification is recorded separately below. No remote
push is authorized.

## Sources and checks

- [Previous classification](../majorana-unitary-stabilizer/results.md).
- [Congruence transport](../../../Math/LinearAlgebra/MajoranaPhaseNormalization.lean).
- [Product coordinates](../../../Math/LinearAlgebra/MajoranaUnitaryClassification.lean).
- [General certificate theorem](../../../Math/LinearAlgebra/UnitaryCongruenceCertificate.lean).
- [Physical input](../../../Physics/FieldTheory/Mass/FlavorMajoranaCertificate.lean).

Acceptance requires explicit inverses, persistent strict transitive axiom
audits, focused and full builds, layout/link/diff checks. The previous topic
was merged into master at `checkpoint 04`; unrelated user documentation edits were
excluded. Merged-state checks and new proof evidence will be recorded here.

## Result

`congruenceEquiv` explicitly conjugates stabilizers in both directions.
`classification` composes it with the existing U/O product coordinates.
`certificateEquiv` and `exists_unique_difference` prove that every Q with the
same target is uniquely `P * S`, with S in the target stabilizer. The set of
certificates is not assigned a group structure. All statements use transpose,
not adjoint, for the bilinear form.

The physics `Input` retains symmetry, real nonnegative diagonal masses, the
unitary basis and the normalization equality as explicit checked data.
`fromDiagonal` constructs such inputs in any supplied unitary basis.
`ofSymmetric` constructs the certificate directly from any finite symmetric
matrix, and `fromDiagonal_surjective` proves that the parametrization is complete.
`form_symmetric` and `subgroup_eq` connect to the actual symmetric bilinear
form and existing mass-stabilizer API. Both layers expose `residualHomEquiv`
and `residual_nonzero_iff` for arbitrary-dimensional complex consumer modules.

At `checkpoint 02` this was conditional classification only. The subsequent
[existence extension](existence.md) proves Takagi existence and completeness
of `fromDiagonal`. Simultaneous Yukawa classification remains excluded.
Equivalences are algebraic; no continuously chosen basis, topology or model
matching is added.

## Certificate milestone verification (stage 01, `checkpoint 02`)

- Focused `lake build Math.LinearAlgebra.Audit.AuditUnitaryCongruenceCertificate
  Physics.FieldTheory.Mass.Audit.AuditFlavorMajoranaCertificate` passed. The
  final constructor extension also passed its focused Physics audit.
- Persistent strict transitive audits: 11 Math and 8 Physics declarations;
  only `propext`, `Classical.choice`, `Quot.sound` allowed.
- Full `lake build` passed (6064 jobs). No new-source warnings; existing
  dependency warnings replayed. Intermediate elaboration failures were fixed.
- Layout and local-link checks and `git diff --check` passed.
- No pins, dependencies, custom axioms, audit exceptions or resource limits
  changed. No operator normalization scripts rerun: their definitions are
  unchanged. Unrelated dirty user documentation remains excluded.
- Both original frozen endpoints were complete. Takagi existence was then
  unproved; it is now proved in the separately recorded extension.

## Integration

Proof milestones: `checkpoint 02` (certificate transport and basis freedom),
`checkpoint 03` (Takagi existence and physical input). The user authorized master
integration at stage 01. Integration uses a clean separate worktree, excluding
unrelated user documentation edits; branches are retained and no push is made.
This closure update is documentation-only: links/diff are checked without a
new pre-merge Lean build. The merged-state build and audits are rerun after merge.

Master merge `checkpoint 01` includes proof milestones `checkpoint 02`, `checkpoint 03` and
closure documentation `checkpoint 05`. Merged-state verification passed:

- `lake build`: 6067 jobs; existing dependency warnings only.
- Fresh `lake env lean` of `AuditTakagiExistence`,
  `AuditUnitaryCongruenceCertificate` and `AuditFlavorMajoranaCertificate`:
  12, 11 and 11 strict transitive checks respectively.
- Layout: 1014 modules. Links in the clean master worktree: 358 Markdown
  files, 2260 links, 34 fragments, zero errors. Diff check passed.

This integration-record follow-up is documentation-only; links/diff are checked
again, without another Lean build. Branches are retained, no remote push is
performed, and unrelated dirty user files are preserved outside the merge.
