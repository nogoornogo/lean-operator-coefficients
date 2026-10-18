# Fifth color/weak slice verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](colored-fifth-slices-results.md).

The three modules preserve the structural audit's numerical-import exclusion,
strict axiom allowlist, dependency pins and default proof limits. The
Clebsch-Gordan labels are small structural tensor degrees; no numerical
dimension, character coefficient, multiplicity or rank certificate is used.

Focused checks use the one-thread guard, 6 GiB sampled process-group RSS cap,
4 GiB host reserve and 300-second wall cap:

- `ColorWeakMiddleGauge`: final gauge branches, continuity and bound pass,
  9.0 s, peak 4,993,900 KiB.
- `DoubletMiddleProducts`: passed, 7.0 s, peak 4,843,860 KiB.
- `ColorWeakFifthSlices`: all three complete actual slice equivalences pass,
  12.0 s, peak 4,976,416 KiB. Module compile time 8.5 s.
- Final successful focused logs contain zero warnings/errors.

The three modules add 42 strict declarations. The Math structural audit
passes all 1177 checks (6.0 s, peak 5,344,776 KiB); Physics retains its 300
checks. Guarded default `lake build` passes all 7224 jobs including GUT
(10.5 s, peak 6,634,932 KiB), with zero warnings/errors and no resource guard
triggered.

Layout passes all 1848 modules. Links pass 930 Markdown files, 5737 local
links and 111 fragments, with zero errors. The retirement check passes 19
hashes and confirms 15 retired modules remain absent. New-module proof-token
and limit scans and `git diff --check` are clean. Disposable output remains
under `/tmp`.
