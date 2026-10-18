# Q joint presentation verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](q-joint-presentation-results.md).

Focused builds are serialized and guarded at 6 GiB sampled process-group
RSS, 4 GiB host reserve and a 45 s wall cap for the new bounded adapters.

- `SU3DoubleSpinAllPresentation`: 4296 jobs, success; guarded 7.8 s,
  sampled peak 4994792 KiB.
- Actual `SMQJointPresentation`: 4572 jobs, success; guarded 5.0 s,
  sampled peak 5139176 KiB.
- Two unspecified projection-type comparisons in the first atom prototype
  reached the unchanged 200000-heartbeat default. Explicit coordinate types
  fixed the issue; the complete atom module then passed in guarded 5.3 s,
  sampled peak 4938504 KiB. No Lean limit was raised.
- Math structural strict audit: 1970 transitive declarations passed;
  guarded 6.3 s, sampled process-group peak 5406248 KiB.
- Physics structural strict audit: 313 declarations passed; guarded 5.0 s,
  sampled peak 5515664 KiB. Total structural checks: 2283.
- Default `lake build`: 7310 jobs including GUT; success, zero warnings or
  errors. Guarded 11.0 s, sampled process-group peak 6665792 KiB. Full-build
  guards (10 GiB process group, 4 GiB host reserve, 300 s wall) did not trigger.
- Layout: 1924 modules, layer/import/cycle/aggregate checks pass.
- Links: 952 Markdown files, 5862 local links, 111 fragments, zero errors.
- Retirement: 19 snapshot hashes verified; all 15 retired numerical modules
  remain absent from active imports.
- New/changed proof token and limit scans and `git diff --check` pass.
  Root README and dependency pins are unchanged.

Development also used bounded disposable prefix probes to isolate type
comparisons. Two overlapping probes were interrupted and rerun serially
with distinct log paths. Final verification is serialized. No numerical
certificate is evaluated, and original endpoint 2 remains open.
