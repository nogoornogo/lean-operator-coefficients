# Sixth and conjugate branching verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](colored-sixth-results.md).

The structural numerical import exclusions, strict axiom allowlists,
dependency pins and default proof limits remain unchanged.

Focused checks use the one-thread guard, 6 GiB sampled process-group RSS cap,
4 GiB host reserve and 300-second wall cap:

- `ColorWeakSixthSlices`: all four source comparisons pass, 14.8 s,
  peak 5,001,704 KiB. The final product rearrangements are explicit coordinate
  tuples with both inverse laws and full equivariance proved in Lean.
- `ColorWeakSixthAssembly`: complete source assembly passes, 14.0 s,
  peak 5,025,920 KiB; module compile time 10 s.
- `SU3DoubleSpinSixth` and the initial Physics positive endpoint pass
  their dependency build, 7.3 s, peak 5,092,476 KiB.
- `ExteriorDualEquivalence`: existing mathlib perfect pairing plus local
  equivariance pass, 3.8 s, peak 3,371,812 KiB.
- `SU3DoubleSpinDuality`: uniform conjugate-core exterior transport passes,
  5.3 s, peak 4,843,968 KiB.
- Final signed-sixth dependency build, including signed fifth/seventh Math
  endpoints: passed, 10.8 s, peak 5,102,820 KiB.
- Final successful focused logs contain zero warnings/errors.

For conjugate degree seven, double-dual normalization is applied to the
actual finite exterior source before its proved branching equivalence.
This avoids needing a new typeclass synthesis path through the large nested
branch carrier. No reflexivity or dimension premise was added.

The Math additions/extension add 57 strict checks, and Physics adds four
endpoint checks. Math passes all 1264 checks (6.3 s, peak 5,351,520 KiB);
Physics passes all 306 checks (9.8 s, peak 5,477,636 KiB), including signed
fifth/seventh adapters. Guarded default `lake build` passes all 7235 jobs
including Math, Physics and GUT (11.8 s, peak 6,629,688 KiB), with zero
warnings/errors and no resource guard triggered.

Layout passes all 1859 modules. Links pass 935 Markdown files, 5762 local
links and 111 fragments, with zero errors. The retirement check passes 19
hashes and confirms 15 retired modules remain absent. New/extended-module
proof-token and limit scans and `git diff --check` are clean. Disposable
output remains under `/tmp`.
