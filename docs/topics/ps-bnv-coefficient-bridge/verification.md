# Verification And Stopping Record

## Planning Checkpoints

The frozen plan was recorded in `checkpoint 01`, with final minimal-PS Phase 4 added
in `checkpoint 02`. Those documentation-only checkpoints had local-link/diff checks
and did not rerun Lean. The topic base remains
`checkpoint 03`; the earlier master integration baseline
is owned by the [species-surplus record](../species-copy-surplus/verification.md).

## Implementation Verification

On `proof/ps-bnv-coefficient-bridge`:

- Focused build:
  `lake build Math.RepresentationTheory.Audit.AuditSymbolicCoefficientBridge GUT.PatiSalam.Audit.AuditCoefficientBridge`
  passed, 3338 jobs.
- Math audit: 12 strict transitive axiom checks and Math-layer import checks.
- PS audit: 52 strict transitive axiom checks and no imports from other GUT
  model applications. The only permitted axioms are propext, Classical.choice
  and Quot.sound; no custom axioms, sorry or allowlist changes.
- Serialized `lake build` passed, 6636 jobs; no warnings/errors in that run.
- `node tools/layout/check-layout.mjs` passed: 1309 modules, layer/import/cycle,
  aggregate registration and relocation audit checks.
- `python3 tools/ps-bnv-coefficient-bridge/audit_ps.py` passed: eight exact
  rational/Gaussian-rational, epsilon and Grassmann controls. Supplementary
  diagnostics are not theorem premises.
- `node tools/docs/check-links.mjs` passed: 592 Markdown files, 3765 local inline
  links, 89 heading fragments, zero errors. The read-only checker ran with
  sandbox escalation because its git subprocess requires it in this environment.
- `git diff --check` passed after staging the new sources and documents.

Source review checked actual invariance, dual/Higgs charges, exterior
projection for repeated species, physical scalar/current signs, complex barred
projection, the full exact mu=0 kernel, actual light-field probes and separate
LR/RR cancellation controls. The existing general completeness framework and
all dependency pins are unchanged. Reusable helpers and their audit are in
Math; the PS application and audit are in GUT. No numerical phenomenology,
loops, rates, new environments or external messaging were used.

## Endpoint Classification

The exact conditional component certificate is verified. The fully normalized
paper-to-model matching remains unverified: M is kept independent because the
source's vertex/VEV/mass sqrt(2) conversion has not been justified in our
specified dictionary. A selected effective Higgs direction from Phi is an
explicit supplied input, not a proved general two-Higgs adapter. The complete
normalized Phase 4 paper comparison is not marked complete. These are the
frozen convention/admission gate, recorded as a bounded stop in the
[result](result.md) and [conventions](conventions.md).

The exact real control also satisfies M=y*star(v), but it is not a canonically
normalized or fitted finite-mu spectrum. A nonzero generated coefficient of
this supplied component path is not a decay-rate or all-channel stability
claim. The branch is committed as a verified checkpoint; no master merge is
authorized by this endpoint.
