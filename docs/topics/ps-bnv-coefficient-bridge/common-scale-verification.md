# Common-Scale Verification

- Branch: proof/ps-bnv-coefficient-bridge; base checkpoint 01; no master integration.
- Focused `lake build GUT.PatiSalam.Audit.AuditActionComparison`: passed,
  3352 jobs and 21 strict transitive checks (only propext, Classical.choice,
  Quot.sound), including both new theorems; model import boundary passed.
- Serialized `lake build`: passed, 6658 jobs. Existing audit info replayed;
  no new proof warnings/errors observed.
- `node tools/layout/check-layout.mjs`: 1331 modules; passed.
- `python3 tools/ps-bnv-coefficient-bridge/audit_ps.py`: 13 exact tests passed;
  supplementary checks, not proof premises.
- Publication PDF downloaded to /tmp and pages 2–4 rendered with pdftoppm;
  compared visually with v2. No PDF/image artifacts added to source control.
  Web PDF screenshots failed; local rendered pages supplied the visual check.
- Initial link check hit sandbox child-process EPERM; rerun recorded below.
- No dependency, resource, axiom allowlist or source import change. Existing
  audit and aggregate registration reused.

- Link-check rerun with sandbox child-process permission: 614 Markdown files,
  3877 local inline links, 89 fragments; zero errors.
- `git diff --check`: passed; reviewed theorem hypotheses and two-gate scope.
