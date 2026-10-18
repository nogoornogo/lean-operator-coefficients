# Math / Physics / GUT Layout

- ID: math-physics-gut-layout
- Status: completed
- Working branch: `refactor/math-physics-gut-layout`
- Integration target: `master`
- Result type: source/documentation refactoring, not a new theorem

## Endpoint

Organize sources by mathematical subject, shared physics, and GUT application.
Enforce imports from GUT to Physics/Math and from Physics to Math, never the
reverse. Keep group-specific mathematical constructions in Math when their
dependencies are mathematical; retain genuine application adapters in GUT.

Preserve declaration names, theorem statements, proof bodies, dependency pins,
axiom allowlists and the explicit E6 literature-input boundary. Extract only
existing generic sections needed to remove accidental upward imports. Namespace
renaming, new foundations, new dependencies and upstream submission are out of
scope. Historical document claims remain historical.

## Deliverables And Acceptance

1. Subject-based Math, Physics and GUT trees, with audits next to their subject.
2. Lake libraries, aggregate imports, generator paths and documentation links
   updated together; old-to-new path map retained for navigation and review.
3. Automated layer/import coverage checks. Historical import-boundary audits
   continue to check original module identities after relocation.
4. Focused builds, existing strict axiom audits, full `lake build`, documentation
   link tests and `git diff --check` pass before integration.

## Result

- 263 existing modules relocated; 530 total modules including library roots and
  the new audit/helper modules. Lake still has one default full-project target.
- [Layout](../../architecture/MODULE_LAYOUT.md), root/layer READMEs, import
  commands, certificate-generator import and documentation links updated.
- [Eight section splits](EXTRACTIONS.md) remove accidental upward dependencies.
  Against the base commit, 509 of 517 original modules have identical bodies
  after excluding imports and the audit identity-normalization line. The eight
  moved sections were checked byte-for-byte against their original bodies.
- [Layer checker](../../../tools/layout/README.md) guards dependencies, missing
  local imports, cycles, aggregate coverage and historical audit identities.
- Source paths change; declaration namespaces remain unchanged. No dependency
  pins, proof hypotheses, E6 literature inputs or axiom allowlists changed.

## Verification

- `node tools/layout/check-layout.mjs`: 530 modules, all checks passed.
- `node --test tools/layout/test-check-layout.mjs`: 9 tests passed.
- `node tools/docs/check-links.mjs`: 219 documents, 1153 local links, no errors.
- `node --test tools/docs/test-check-links.mjs`: 5 tests passed.
- `python -m unittest discover -s tools/e6 -p 'test_*.py'`: 10 tests passed.
- Focused `lake build Math.Audit.AuditExtractedInterfaces
  GUT.SU6.Adapters.CompactProductClassification`: passed, 3870 jobs; 26 strict
  transitive axiom checks passed.
- Direct `lake env lean` replay of the relocated `AuditLiteratureTopology` and
  `AuditAbelianMassSpectrum`: passed. E6 surjectivity remains an explicit input.
- Full `lake build`: passed, 5545 jobs (stage 01). The initial pass found a
  mixed SU2/SU3 application section; after separation, both focused and full
  builds passed. Existing deprecation/style/unused-variable warnings remain;
  no proof changes were made merely to silence them.
- `git diff --check` and staged diff check: passed.

No fresh-clone reproduction or doc-gen4 regeneration was run. Existing generated
HTML may still have old module URLs; regenerate using the updated documentation
command when needed. Build output stays under ignored `.lake/`, not in the topic.

## Closure

No proof obligations were opened or closed by this refactor. Old import paths
must be updated; existing declaration names remain available under the new
imports. Integration target is `master`; Git ancestry records the topic commit
and merge. Retain the topic branch. No remote push is part of this task.

## Additional mathematics relocation

See the [low-rank relocation record](low-rank-relocation.md) for the later
six-module source move and its focused audit and full-build evidence.
