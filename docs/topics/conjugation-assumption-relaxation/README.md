# Conjugation Assumption Relaxation

- ID: conjugation-assumption-relaxation
- Status: completed
- Result type: both sufficient-hypothesis relaxations proved simultaneously
- Working branch: `proof/conjugation-assumption-relaxation`
- Integration target: `master`
- Integration evidence: Git ancestry; integrate only after the completion gate

## Frozen Endpoint

Keep the three actual conjugations, fixed SM torus, finite-dimensional complex
matter, commuting Abelian residual action, invariant symmetric mass and exact
dual light target. Change only these two inputs:

1. Replace `Family` and its common positive species total by arbitrary finite
   nonnegative profiles P with `0 < total P.quark` and `0 < total P.down`.
   The two totals need not agree. Derive the orbit profile equalities as before;
   do not assume them.
2. Require unitarity only of `StructuralConjugation.restrict j rho`, not of the
   entire ambient representation rho.

Prove the same actual resolved-radical endpoint: nonzero modes at all fifteen
selected SM weights, supported neutral `qque`/`duql` signatures, and failure
of universal prohibition in the existing dimension-six signature class.

## Milestones And Acceptance

| ID | Deliverable | State |
| --- | --- | --- |
| AR-1 | Positive-total charge selection without common totals; retain old API; unequal-total algebraic control | Completed |
| AR-2 | Restriction-unitary actual mass spectrum and combined endpoint; old theorem/spectrum recovery | Completed |
| AR-3 | Persistent strict axiom/import audits, regression, scope documentation, integration | Completion gate passed; merge evidence in Git ancestry |

Use existing mass/index, character and eigenvector APIs. Preserve prior checked
declarations and the three conjugation interface. Extract a shared core only
where necessary to avoid duplicated spectrum proofs. A type-checked consumer
must need neither a `Family` nor ambient unitarity. Include finite residual
charges and a profile example with unequal totals; the latter is coefficient
algebra, not an anomaly-consistent physical benchmark.

## Stop Condition And Non-Goals

Stop after the two relaxations and compatibility checks succeed, or report the
specific blocked implication if these frozen hypotheses are insufficient.
No new Lie theory, dependencies, anomaly theorem, weakening of the exact target,
non-Abelian symmetry, or new physical model classification is authorized.
Keep the E6 literature boundary and signature-versus-amplitude distinction.
Removing common totals does not assert quantum consistency of unequal matter.

## Work And Verification

The two positive-total selection lemmas compile. The finite-residual control
has totals 2 for Q/up/electron and 1 for down/lepton; Lean proves both the
absence of any common total and the supported-neutral coefficient endpoint.
The four-declaration strict audit passed (3081 jobs); layout passed (549 modules).
Full regression passed (5565 jobs), with document links and diff checks clean.
AR-2 proves the combined endpoint in `StructuralConjugationMass.RestrictedUnitary`.
The previous mass module now wraps this core without changing its public theorem
types. The old actual radical spectrum is definitionally the new spectrum.
The new focused audit passed (3820 jobs, 10 strict checks); existing mass and
SU(5)-chain adapter audits passed (3928 jobs). Full regression passed (5567 jobs),
and layout passed for 551 modules. Existing unused-section-variable warnings
remain in `Math/LinearAlgebra/FiniteBasisHilbertization.lean`; no new warnings.
No proof obligation remains in the frozen scope. Integrate with `--no-ff` and
retain the branch. The [result record](results.md) gives declarations, commit
references, controls and boundaries. The current
[criterion](../../proof/current/inputs/Physics/STRUCTURAL_CONJUGATION.md) states the weaker assumptions.
Lean LSP MCP is unavailable in this session; use focused builds.
Acceptance requires focused audits, full `lake build`, layout checks, document
links and `git diff --check`. Only `propext`, `Classical.choice`, `Quot.sound`
are allowed in strict transitive axiom audits. Commit per milestone, merge
with `--no-ff`, retain the branch; no remote push.

## References

- [Previous criterion](../../proof/current/inputs/Physics/STRUCTURAL_CONJUGATION.md)
- [Source and conjugation interface](../../../Physics/StandardModel/Spectrum/ConjugationSource.lean)
- [Existing mass consumer](../../../Physics/StandardModel/Spectrum/ConjugationMassSource.lean)
- [Finite profiles](../../../Physics/StandardModel/Spectrum/FiniteChargeProfiles.lean)
