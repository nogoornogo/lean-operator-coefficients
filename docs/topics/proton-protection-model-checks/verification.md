# Verification

## Evaluation Endpoint

- `lake env lean GUT/Common/ProtonProtection/ModelControls.lean`: passed.
- `lake build GUT.Common.ProtonProtection.Audit.AuditModelControls`: passed,
  3,893 jobs; seven strict transitive axiom checks, allowing only `propext`,
  `Classical.choice`, `Quot.sound`.
- Serialized `lake build`: passed, 6,619 jobs, including registered audits and
  the updated aggregate. Focused new-module checks reported no warnings.
- `node tools/layout/check-layout.mjs`: passed, 1,292 modules; layer/import,
  cycle, aggregate coverage and relocation checks.
- `python3 tools/proton-protection-model-checks/audit_models.py`: seven exact
  deterministic controls passed. No numerical approximation or extra package.
- `node tools/docs/check-links.mjs`: passed, 569 Markdown files, 3,655 local
  links and 88 heading fragments, zero errors. A sandbox subprocess EPERM
  was resolved by rerunning the same read-only command outside that restriction.
- `git diff --check`: passed.

The all-flavor proof initially hit the default elaboration heartbeat limit
while matching independently inferred index universes. Specifying the common
universe explicitly resolved it; no heartbeat limits or dependency pins changed.
No custom axioms, sorry or audit exceptions were introduced.

The final review distinguishes supplied UV branching/VEV dictionaries, proved
conditional physical-sector certificates, supplementary exact calculations and
unproved full-model adapters. See [phase contracts](phase-contracts.md),
[conditional dossier](../../proof/current/applications/GUT/PROTON_PROTECTION_MODEL_CONTROLS.md),
and [the endpoint](evaluation-result.md). No original-model all-mass admission
or all-loop proton-stability theorem is claimed. Source versions and paper
links are retained in [the source register](sources.md) and model records.

## Planning Checkpoint

Commit `checkpoint 01` established the staged plan and model-study homes only.
Documentation links and whitespace passed; no Lean build was rerun for that
checkpoint. The first link check found this missing record and passed after it
was added; a subprocess EPERM retry used the same read-only link command.

## Integration

Working branch: `proof/proton-protection-model-checks`. Base:
`checkpoint 02`. Endpoint: `checkpoint 03`.
Explicit user-directed no-fast-forward integration into master:
`checkpoint 04`.

Merged-state checks passed: serialized `lake build` (6,619 jobs, including
registered audits; no warning/error lines), layout (1,292 modules), seven exact
model controls, local links (569 files, 3,655 links, 88 fragments), and whitespace.
The first merge attempt stopped for missing committer identity; command-local
identity completed the merge without changing repository/global configuration.
No remote push was made. Local topic cleanup follows the reachability/worktree
checks; the historical working-branch name remains recorded above.
