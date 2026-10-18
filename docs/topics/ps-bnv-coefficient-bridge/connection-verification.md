# Connection Verification

- Branch: proof/ps-bnv-coefficient-bridge; base checkpoint 01.
- Result: selected component-action connection and restricted compatibility
  obstruction; full paper/source convention admission unverified.
- Focused `lake build Physics.FieldTheory.Mass.Audit.AuditWeylGrassmannAction GUT.PatiSalam.Audit.AuditCoefficientBridge`:
  success, 3344 jobs. Four shared Physics and 88 PS strict transitive axiom
  checks; only propext, Classical.choice, Quot.sound accepted. Physics imports
  no model layer; the PS audit retains its other-model exclusion.
- Serialized full `lake build`: success, 6642 jobs; no warning/error diagnostics.
- `node tools/layout/check-layout.mjs`: 1315 modules; layers/imports/cycles,
  aggregate coverage and relocation audits OK.
- `python3 tools/ps-bnv-coefficient-bridge/audit_ps.py`: ten exact tests passed.
  New controls use actual Grassmann multiplication for the symmetric mass half
  and rational common-factor compatibility. Real.sqrt(2) is proved in Lean,
  not approximated in the script.
- `node tools/docs/check-links.mjs`: 599 Markdown files, 3803 local inline
  links, 89 heading fragments, zero errors.
- `git diff --check`: clean before commit.
- No dependency pin, audit allowlist, custom axiom or proof resource policy changed.

Early sum-expansion and coercion proof failures were corrected before acceptance.
The existing Euclidean four-component adapter was reused after source inspection;
it was not treated as the source paper's physical convention by default.
The exact result and its restrictions are in [connection-result](connection-result.md).
