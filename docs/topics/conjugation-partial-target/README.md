# Partial SM Target Under Actual Conjugations

- ID: conjugation-partial-target
- Status: completed
- Result type: local SM dual-index matching suffices; previous full target recovered
- Working branch: `proof/conjugation-partial-target`
- Integration target: `master`
- Integration evidence: Git ancestry after the completion gate

## Frozen Endpoint

Keep the three actual ambient conjugations, fixed SM torus, finite-dimensional
complex representation of `G x H` (H Abelian), unitarity only of its `T x H`
restriction, invariant symmetric mass, and separate positive Q/down totals.

Replace global equality to the SM-plus-singlet dual light character by equality
of the actual radical's dual-index coefficients at the fifteen oriented SM
weights, for every residual character. Impose no matching condition at other
weights. The supplied profiles are finite and nonnegative. Profile equality,
radical invariance under conjugation and operator support remain conclusions,
not premises.

Derive the same occupied neutral `qque`/`duql` signatures and actual nonzero
radical eigenvectors at all fifteen selected weights. Recover the full-target
theorem as a special case, on exactly the same actual spectrum.

## Bounded Plan

| ID | Deliverable | State |
| --- | --- | --- |
| PT-1 | Derive actual dual-index coefficient invariance without a full Laurent target, using faithful finite character evaluation | Completed |
| PT-2 | Local target, profile compatibility, support and full endpoint; full-target adapter | Completed |
| PT-3 | Extra-sector algebraic controls, strict axiom/import audits, full regression, documentation and integration | Completion gate passed; merge evidence in Git ancestry |

Use finite polynomials on all actual scalar characters, so no ambient torus
weight-classification theorem is required. A bounded Math helper may transport
coefficients under a group automorphism using the existing faithful evaluator.
Conserve the dual mass index before applying ambient conjugation; do not
assume the radical representation is conjugation-invariant.

## Controls And Stop Gate

- A consumer must not assume a global target or an ambient-unitarity certificate.
- Full target implies the local coefficient condition on the same spectrum.
- Additional finite sectors with zero dual contribution at the monitored
  weights preserve the local condition. Show a coefficient-level extra sector
  with nonzero dual index away from SM; this is not a new physical GUT model.
- Strict audits allow only `propext`, `Classical.choice`, `Quot.sound`.
  Check Physics imports no GUT application modules. Preserve old APIs and pins.

Stop after this endpoint or on a specific failed implication; do not add new
representation classification, anomaly theory, alternative symmetry classes,
or quantum dynamics. This does not allow arbitrary extra matter at the monitored
weights: its *dual* contribution there must satisfy the local condition.
The E6 literature boundary and signature-versus-amplitude distinction remain.

## Verification And Next Action

PT-1: focused audit passed (3820 jobs, 7 strict checks); full `lake build`
passed (5570 jobs), layout passed (554 modules). The finite-character transport
lemma and actual dual-index bridge require no full target or radical invariance.
PT-2: the local target supplies profile compatibility, actual nonzero modes and
the same neutral signature pair. A full target implies the new local input on
the identical spectrum. Focused audit passed (3822 jobs, 15 strict checks),
full build passed (5573 jobs), and layout passed (557 modules).
PT-3: an exotic dual-index component preserves local matching but violates any
full target with the same profiles and arbitrary singlets. An opposite-SM-weight
contaminant fails local matching despite vanishing at positive SM weights.
These are coefficient-level controls, not new physical models. Focused audit:
3084 jobs, 6 checks. Final full build: 5574 jobs; layout: 558 modules.

No proof obligation remains in the frozen scope. See the [results](results.md)
for all 28 new strict checks, source declarations and applicability boundaries.
Integrate with `--no-ff` and retain the topic branch; no new task is implied.
Lean LSP MCP is unavailable; use focused builds, then full `lake build`, layout,
local link checks and `git diff --check`. Commit verified milestones, merge
with `--no-ff` after completion, retain the branch and do not push remotely.

## References

- [Current criterion](../../proof/current/inputs/Physics/STRUCTURAL_CONJUGATION.md)
- [Previous relaxations](../conjugation-assumption-relaxation/README.md)
- [Restricted-unitary mass core](../../../Physics/StandardModel/Spectrum/RestrictedConjugationMassSource.lean)
- [Actual finite-character polynomials](../../../Math/RepresentationTheory/Characters/AbelianCharacterPolynomial.lean)
- [Mass conservation](../../../Physics/FieldTheory/Mass/AbelianMassSpectrum.lean)
