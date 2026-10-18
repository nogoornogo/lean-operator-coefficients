# Li Weinberg LLHH Basis Verification

- ID: `li-weinberg-basis`
- Status: completed
- Result type: proved normalized local certificate and finite flavor counting
- Working branch: `proof/li-weinberg-basis`
- Integration target: `master`
- Integration evidence: merged into `master` by `checkpoint 01` on explicit user direction

## Endpoint And Scope

Certify the normalized local interpretation of Li et al.'s Weinberg `LLHH`
candidate against the independently defined existing Weinberg sector, rather
than assuming the paper's completeness claim. Prove actual candidate assembly
and coordinate extraction are mutually inverse, including mixed statistics and
finite flavor coordinates.

Keep the existing assumptions: one Higgs doublet with trivial residual action,
an arbitrary residual group `R`, and an arbitrary complex lepton multiplicity
representation `F`. Finite bases are additional inputs only for counting.
The target remains `Hom_R(Sym² F, trivial ℂ)`; no compactness, continuity,
self-duality or finite-dimensionality is imposed on the general theorem.

This is a literature-candidate certificate, not a new all-sector ΔL=2
classification. Derivatives, EOM/IBP, amplitudes, general p/y/m/j algorithms,
multiple Higgs fields, seesaw matching and numerical phenomenology are excluded.

## Deliverables And Acceptance

- [Plan and stop gates](plan.md).
- A source dictionary with visually checked equation/page, field order,
  weak/spinor brackets, exchange signs and normalization.
- Separate convention/certificate modules for LLHH, with a persistent strict
  transitive axiom audit and aggregate registration.
- A completed-result dossier `docs/proof/Physics/LI_WEINBERG_BASIS.md`,
  proof-index and verified-assumptions updates at acceptance.

## Work And Open Obligations

All five planned milestones are complete. The [source dictionary](source-recovery.md) identifies page 38 Out[7].
Literal assembly, mixed exchange laws, both inverses, actual-field transport,
finite symmetric coordinates and dimension formula, sign-character control and
Majorana evaluation are proved. No obligations remain in the bounded endpoint.
Integration and merged-state verification are complete.

## Result And Verification

Focused build of `Physics.StandardModel.Operators.Audit.AuditLiWeinbergBasis`
passed (3793 jobs), including 24 strict transitive axiom checks and exact finite
index controls 0,1,6. No new assumptions or dependency changes were required.
See the [completed-result dossier](../../proof/current/applications/Physics/LI_WEINBERG_BASIS.md).

Final acceptance checks:

- `lake build Physics.StandardModel.Operators.Audit.AuditLiWeinbergBasis`:
  passed, 3793 jobs; 24 strict transitive axiom checks.
- `lake build`: passed, 6403 jobs, no warnings/errors; existing Li family
  audits also replayed successfully.
- `node tools/layout/check-layout.mjs`: 1076 modules, no violations.
- `node tools/docs/check-links.mjs`: 402 Markdown files, 2729 local links,
  99 heading fragments, no errors.
- `git diff --check`: passed. Pins and root README unchanged.

Merged-state checks repeated successfully: `lake build` (6403 jobs, including
24 LLHH strict axiom checks), layout, local links and `git diff --check`.

The acceptance review confirmed that arbitrary-R coordinates retain invariance
constraints and that unrestricted counts require trivial induced Sym² action.
No all-sector dimension-five support classification, amplitude correspondence,
runtime ABC4EFT output or UV-generated coupling is claimed.

## References

- [Existing Weinberg completeness](../delta-l-two-weinberg/README.md)
- [Existing results and boundaries](../delta-l-two-weinberg/results.md)
- [SM field interface](../../../Physics/StandardModel/Operators/WeinbergSMInterface.lean)
- [DUQL/DUUE certificate precedent](../li-duql-duue-basis/README.md)
- [Li et al., arXiv:2201.04639v2](https://arxiv.org/abs/2201.04639v2)

The paper is a source of candidate expressions, not a trusted Lean premise.
