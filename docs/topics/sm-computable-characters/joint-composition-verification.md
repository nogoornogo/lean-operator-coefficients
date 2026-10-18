# Joint composition verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](joint-composition-results.md).

Focused checks are serialized with one Lean thread, a sampled 6 GiB
process-group cap, 4 GiB host reserve and 300 s wall cap. No proof limits,
dependency pins, literature premises or audit exclusions are changed.

- Math structural strict audit: 1855 transitive declarations passed;
  guarded 18.8 s, sampled process-group peak 5407608 KiB. This also rebuilt
  all final source, dual, zero-source and placement helpers without warnings.
- Physics structural strict audit: 306 checks passed; cached replay 2.8 s,
  sampled process-group peak 879500 KiB. Total structural checks: 2161.
- Default `lake build`: 7301 jobs including GUT; success, no warnings or
  errors. Guarded 8.5 s, sampled process-group peak 6663644 KiB. Full-build
  guards (10 GiB process group, 4 GiB host reserve, 300 s wall) did not trigger.
- Layout: 1915 modules, layer/import/cycle/aggregate checks pass.
- Links: 950 Markdown files, 5850 local links, 111 fragments, zero errors.
- Retirement: 19 snapshot hashes verified; all 15 retired numerical modules
  remain absent from active imports.
- New source token/limit scans and `git diff --check` pass. Root README and
  dependency pins remain unchanged.

This verifies the joint expression interface; the actual all-content SM
consumer remains open. No numerical certificate was used.
