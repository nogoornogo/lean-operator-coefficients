# Maintained assignments and degree bounds

## Implemented interfaces

`SMChargeDegreeBounds` proves the signed pattern inequality `|B3|+|L|≤n`,
selected-B bounds, and the corresponding twice-engineering-dimension grading
`3*n+2*(h+d)`. It connects nonzero original coefficients to even degree,
even B3+L and exact residual charge. An explicit arithmetic minimum-|L| gate
then gives an all-content/all-Higgs degree lower bound. No minimum total
dimension or UV/decay interpretation is asserted.

`verify-assignments.py --output /tmp/NEW-DIRECTORY` is the named opt-in target.
It builds local imports, verifies retained hashes and exact CSV agreement,
requires the original kernel/strict-audit marker, then kernel-checks 796
all-content degree bounds. The original generated source identity is unchanged.
Temporary files/logs stay in the selected fresh directory. The normal library
build checks the general degree interface and persistent audit; it does not
implicitly execute the 572-row regression target.

The selected |L| distributions give 278 B1 rows with |L|≥3 and 284 B2 rows
with |L|≥2. The closed arithmetic gates exclude every smaller absolute L,
not just a particular witness. Thus every allowed content in those groups
requires respectively n≥6/D≥9 and n≥8/D≥12. The exact minima may be larger.

## Verification and failures

The focused degree build passes (5.0 s, sampled group peak 5207840 KiB).
Its persistent audit passes all 13 public declarations (4.8 s, 5159232 KiB).
Strict audits allow exactly propext, Classical.choice and Quot.sound.

During verifier development the first import build failed because
`Lean.Util.CollectAxioms` is a toolchain module, not a Lake module target
(1.3 s, 825852 KiB). The verifier now builds only repository-local imports;
toolchain imports are checked when Lean reads the generated file. The corrected
original certificate run passes in 70.0 s, 6940096 KiB, all 3724 strict checks.

The first lower-bound certificate attempt failed on cast simplification and
unused-variable warnings (40.1 s, 6074752 KiB). Normal cast transport and
explicit underscore names correct those issues. The second attempt elaborated
the lower-bound declarations but failed in the final audit's untyped counter
(84.7 s, 7012868 KiB); giving the counter type Nat corrects that error.
Neither failed file is an accepted kernel certificate. No proof option,
resource limit, dependency, source support definition or audit allowlist changed.

The final combined target passes: original certificates 62.2 s, 7061352 KiB,
3724 strict checks; all 796 degree bounds 84.7 s, 7018012 KiB, 2812 strict
checks. The generated original source retains SHA256 `checkpoint 01…`; the exact
hashes, distributions and import measurements are in the
[machine-readable record](stage-one-verification.json).

The serialized full default-root `lake build GUT` passes all 7337 jobs,
zero warnings/errors, 9.0 s, 6694616 KiB sampled group peak. Layout passes
1951 modules; local links and diff checks pass. Python syntax checks pass.
All checks retain one Lean thread, 300 s/10 GiB/4 GiB reserve guards and
unchanged pins/options. No merge or push occurred. Stage 1 is complete;
the next action is the bounded finite-set proof stage.
