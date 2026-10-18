# Action Translation Verification

- Branch: proof/ps-bnv-coefficient-bridge; base checkpoint 01; no master merge.
- Focused `lake build Physics.FieldTheory.Mass.Audit.AuditChiralActionConvention GUT.PatiSalam.Audit.AuditCoefficientBridge`:
  success, 3346 jobs; 11 shared Physics and 101 PS strict transitive axiom
  checks, accepting only propext, Classical.choice, Quot.sound. Layer/model
  import checks retained.
- Serialized full `lake build`: success, 6645 jobs, no warning/error diagnostics.
- `node tools/layout/check-layout.mjs`: 1318 modules; layers/imports/cycles,
  aggregate coverage and relocation audits OK.
- `python3 tools/ps-bnv-coefficient-bridge/audit_ps.py`: eleven exact tests passed;
  Gaussian-rational Grassmann dagger reverses products and conjugates couplings,
  including differentiated generators for the kinetic identity. No floating
  evolution, simulation or added dependency.
- `node tools/docs/check-links.mjs`: 602 Markdown files, 3818 local inline
  links, 89 heading fragments, zero errors.
- `git diff --check`: clean before commit.
- Early proof failures and unused-section warnings were corrected without
  linter/resource-policy changes. No pins, custom axioms or audit allowlists changed.

The exact same-convention discrepancy is proved in Lean. Script success does
not establish spacetime boundary conditions, an unprinted kinetic action or
all possible source conventions. See the [result](action-translation-result.md).
