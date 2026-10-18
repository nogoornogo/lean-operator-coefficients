# Exterior-weight source verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](exterior-weight-slice-results.md).

Five Math modules add 31 strict transitive checks. The audit allowlist
(`propext`, `Classical.choice`, `Quot.sound`), numerical import exclusions,
Lean/dependency pins and default proof limits are unchanged.

Focused builds use the existing one-thread guard, 6 GiB sampled process-group
RSS cap, 4 GiB host reserve and 300-second wall cap. Successful checks:

- `TorusScalarProductSlice`: 5.8 s, peak 4,302,228 KiB.
- `PatternScalarWeights`: scalar action and occupation-weight identity pass;
  unused-section warnings were removed and the final rebuild is clean.
- `BinaryScalarExteriorSlice`: 6.3 s, peak 4,452,944 KiB.
- `SU2DoubletTorusSplit`: 5.3 s, peak 4,784,676 KiB before the final explicit
  representation type annotation; it was rebuilt in the next check.
- `SU2ExteriorWeightSlice`: 9.0 s including the preceding rebuild,
  peak 4,814,400 KiB. Both modules pass with zero warnings/errors.

An initial inferred tensor equivalence hit the default elaboration heartbeat
limit. The final separate residual-exterior equivalences and explicit tensor
constructor avoid that unification cost. A circle-restriction abbreviation
also needed its explicit `Representation` type for downstream exterior-power
field resolution. No proof limit or mathematical hypothesis was changed.

The strict Math audit passes all 1047 checks (5.8 s, peak 5,339,892 KiB).
The unchanged Physics structural audit retains its 300 checks. Final full
build and repository verification are recorded below. Build logs remain
disposable under `/tmp`.

Guarded default `lake build` passes all 7213 jobs including GUT, with
zero warnings/errors (9.8 s, peak 6,632,252 KiB). No resource guard triggered.
Layout passes all 1837 modules. Local links pass 924 Markdown files,
5717 local links and 111 fragments, with zero errors. The retirement check
passes 19 hashes and confirms 15 retired modules remain absent.
`git diff --check` passes.
