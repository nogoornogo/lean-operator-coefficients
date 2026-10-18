# Weight reconstruction verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](weight-reconstruction-results.md).

Three new Math modules and five extended absent-weight lemmas add 27 strict
transitive checks. The structural numerical-import exclusions and the
allowlist (`propext`, `Classical.choice`, `Quot.sound`) are unchanged.
No dependency pin, numerical certificate or default proof limit changed.

Focused checks use the existing one-thread guard, 6 GiB sampled process-group
RSS cap, 4 GiB host reserve and 300-second wall cap:

- `SU2WeightsDetermine`: passed, 6.3 s, peak 4,886,552 KiB.
- `SU2GroupStrings`: initial complete regrouping passed, 6.3 s,
  peak 4,879,004 KiB; its reconstruction consumer was rebuilt below.
- `SU2ExteriorSliceModels`: final dependency rebuild passes in 9.5 s,
  peak 4,931,000 KiB, including the arbitrary-string reconstruction.
- The five absent-weight extensions pass their dependency rebuild.
- Final successful focused logs contain zero warnings/errors.

The copied-source absent-weight proof initially hit the typeclass heartbeat
limit when a rewrite requested a zero-map instance with unconstrained carrier
metavariables. Supplying the actual linear map's zero identity directly fixed
that inference issue without changing the claim or a proof limit.

The Math structural audit passes all 1135 strict checks (6.0 s, peak
5,342,892 KiB); Physics retains its 300 checks. Guarded default `lake build`
passes all 7221 jobs including GUT (9.8 s, peak 6,634,076 KiB), with zero
warnings/errors and no resource guard triggered.

Layout passes all 1845 modules. Links pass 928 Markdown files, 5730 local
links and 111 fragments, with zero errors. The retirement check passes 19
hashes and confirms 15 retired modules remain absent. `git diff --check`
and the new/extended-module proof-token and limit scan are clean.
Disposable output remains under `/tmp`.
