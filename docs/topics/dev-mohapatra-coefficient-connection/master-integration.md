# Local integration verification

The user authorized integration of the completed proof topic after the literature
linking topic. This does not reopen the investigation or authorize a remote push.

Five conflicts concerned aggregate imports and documentation indexes/ledgers.
Both parents' imports and existing records were retained, with duplicate imports
removed. Individual proof files were unchanged from the proof branch. The
Physics assumptions ledger and application dossier now link the final closure
results as well as earlier checkpoints.

## Proof verification

All commands ran on the resolved merged source tree with unchanged dependency
pins. The bounded runner used one Lean thread, a sampled process-group RSS guard
of 10 GiB, a 4 GiB host-memory reserve and a 300-second budget per invocation.

- Focused build of `Physics.StandardModel.Operators.Audit.AuditDevMohapatraMagnitudeObstruction`:
  passed, 3,990 jobs, 12.5 seconds, sampled peak 845,500 KiB. Cached audit output
  was replayed; fresh individual audits are recorded separately below.
- Full default-target build (`--build GUT` through
  `tools/exact-rank/kernel-probe.py`): passed, 7,415 jobs, no warnings,
  52.6 seconds, sampled peak 6,630,612 KiB.
- Fresh audits: direct `lake env lean` execution through the same bounded runner
  for the six added Math audit files and fourteen Dev–Mohapatra audit files.
  All 20 files passed, totaling 419 strict transitive checks. These check
  transitive axioms and declaration ownership without exceptions.
- All five exact diagnostic scripts under `tools/dev-mohapatra/` passed:
  selected contraction, tree level, literature conventions, fixed-leg sewing
  and Hermitian action. These reproducible scripts are diagnostics, not Lean
  theorem premises.

The result remains conditional on the displayed source adoption, nonzero
couplings/masses and specified normalization families. It does not prove an
unrestricted normalization obstruction, a physical matching prescription or a
phenomenological prediction. No new foundational investigation was undertaken.

## Documentation and integration

The findings summary uses ordinary local evidence links and contains no branch
or integration-status discussion. Work dates and local commit identifiers were
removed from imported documentation; publication metadata, dependency revisions
and source checksums retain their distinct roles.

Final checks passed: 1,083 Markdown files, 6,790 local links and 111 heading
fragments without errors; 1,075 portable evidence files; 145 indexed topics and
145 outcome links; 2,029 modules with valid layout; seven portable-document tests,
five link-checker tests and whitespace checks. Link-checker regression tests
required the same Git subprocess permission as the main link checker. An initial
sandbox invocation failed; the permitted invocation passed all five tests. Both local topic branches were deleted after confirming that master contains
their tips, no worktree uses them and no recorded child topic needs them.
Post-commit metadata, topic-index, link and whitespace checks passed.
No remote push was performed; `docs.zip` is preserved.
