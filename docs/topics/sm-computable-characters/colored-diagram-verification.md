# Labelled-diagram verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](colored-diagram-results.md).

Focused builds use one Lean thread, a 6 GiB sampled process-group RSS cap,
4 GiB host reserve and 300-second wall cap. No proof limits, mathematical
premises, import exclusions, strict audit allowlists or dependency pins change.

- `TensorVolumeEvaluation`, including the complete determinant-block and
  degree-raising formulas: pass in its diagram dependency build, 8.5 s,
  peak 4,885,544 KiB; its own compile took 1.9 s.
- `SU3ContractionDiagram`: final pass, 4.5 s, peak 4,873,540 KiB.
- `SU3MixedContractionSpan` bidual generator extension: pass, 8.8 s,
  peak 4,898,168 KiB, including rebuilt tensor-power equivalences.
- `SU3DualContractionDiagram`: final pass, 8.5 s, peak 4,875,064 KiB,
  including the general contraction formula and defining diagram.
- `TraceFreeColorVertex`, after both local symmetric-slot invariances:
  pass, 17.5 s, peak 4,782,588 KiB, including rebuilt trace/dual prerequisites.
- Final structural Math audit rebuilds the affected endpoints and passes
  all 1505 strict transitive checks, 18.8 s, peak 5,396,960 KiB.
- Physics structural audit passes all 306 unchanged checks by cached replay,
  2.5 s, peak 877,404 KiB.

Four modules and 39 new/extended strict declarations are registered. The
guarded default `lake build`, including Math, Physics and GUT, passes all
7270 jobs in 8.8 s, peak 6,654,196 KiB, with zero warnings/errors and no
resource guard triggered. Its monitor uses a 10 GiB sampled process-group
cap, 4 GiB host reserve and 300-second wall cap. Final successful focused
logs are also warning-free. Disposable output remains under `/tmp`.

Layout passes 1884 modules. Links pass 942 Markdown files, 5787 local links
and 111 fragments with zero errors. The retirement check passes 19 hashes
and confirms 15 retired modules remain absent. New/extended-source
proof-token/limit scans and `git diff --check` are clean.
