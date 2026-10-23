# Verified Master Integration

The user explicitly accepted the bounded derivative/IBP/EOM theorem endpoint
and authorized integration into `master`. The starting worktree was clean;
master was an ancestor of the derivative/IBP parent with no independent target
changes. Recorded child integrations were performed with `git merge --no-ff`:

1. `proof/formal-first-variation` into `proof/gauge-covariance-engineering`.
2. That parent into `proof/nonlinear-eom-gauge-jets`.
3. That parent into `proof/derivative-ibp`.
4. The derivative/IBP parent into `master`.

All merges were conflict-free. Each intermediate merged source tree equals
the verified first-variation tree; master retains the same source tree.
No source, dependency pin, root README or audit allowlist was changed for
integration. The bibliography already contains the final source roles and
result links, including Tong and the first-order field-redefinition boundary.

## Merged-State Verification

Heavy checks used four Lean threads, a 540-second timeout and inherited 16 GiB
per-process address-space bound, with default Lean limits unchanged. The
following focused gate passed before integration and again on master:

```sh
LEAN_NUM_THREADS=4 lake build \
  Math.Algebra.Audit.AuditScalarJetIBP \
  Math.Algebra.Audit.AuditMixedJetIBP \
  Math.Algebra.Audit.AuditDirectionalJetIBP \
  Math.Algebra.Audit.AuditJetEquationIBP \
  Math.Algebra.Audit.AuditJetSpurionEvaluation \
  Math.Algebra.Audit.AuditLinearJetEquation \
  Math.Algebra.Audit.AuditJetEOMCompletion \
  Math.Algebra.Audit.AuditNonlinearGaugeJets \
  Math.Algebra.Audit.AuditGaugeEngineering \
  Math.Algebra.Audit.AuditFirstVariation \
  Physics.FieldTheory.Jets.Audit.AuditLorentzScalarEOM \
  Physics.FieldTheory.Jets.Audit.AuditLorentzSpurionEvaluation \
  Physics.FieldTheory.Jets.Audit.AuditWeylLinearEquation \
  Physics.FieldTheory.Jets.Audit.AuditWeylJetAdjoint \
  Physics.FieldTheory.Jets.Audit.AuditMaxwellLinearEquation \
  Physics.FieldTheory.Jets.Audit.AuditNonlinearGaugeJets \
  Physics.FieldTheory.Jets.Audit.AuditGaugeEngineering \
  Physics.FieldTheory.Jets.Audit.AuditFirstVariation
LEAN_NUM_THREADS=4 lake build
```

Focused gate: 3480 jobs; 18 audit modules report 1323 strict transitive checks.
Only the existing standard axioms are permitted; layer restrictions remain
unchanged. Full master build: 7669 jobs passed. Existing warnings and module
system import recommendations remain; no theorem failure occurred.

Structural and documentation gates passed: 2175 layout modules; 1170 Markdown
files with 7450 local links and 125 heading fragments; 155 indexed topics with
outcomes; 1162 portable metadata files; `git diff --check`. No additional Lean build was needed
for subsequent documentation-only updates.

## Endpoint And Cleanup

All recorded theorem contracts are complete within their own explicit scopes.
Input usability and parity with the derivative-free input interface belong to
a separate topic. General Lagrangian input, analytic variational principles,
quantum equivalence and higher-order field-redefinition equivalence are not
claimed. This integration introduces no new extension.

The four merged working branches are retired locally after reachability and
worktree checks. Historical branch names remain in topic records. No remote
push, remote deletion or unrelated branch/worktree cleanup is included.
