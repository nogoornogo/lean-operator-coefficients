# Color tree verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](colored-tree-results.md).

Focused builds use one Lean thread, a 6 GiB sampled process-group RSS cap,
4 GiB host reserve and 300-second wall cap. No proof limits, dependency pins,
mathematical premises or audit exclusions change.

- Focused `ColorFlagTree` build: 4097 jobs, success (2.3 s for the new module).
- Math strict structural audit: 1581 transitive declaration checks passed.
- Physics strict structural audit: 306 checks passed (cached replay, 2.5 s,
  sampled process-group peak 877912 KiB).
- Full default `lake build`: 7275 jobs, including `GUT`; success, no warnings
  or errors. Guarded elapsed 8.3 s, sampled process-group peak 6656556 KiB;
  no memory, host-reserve or wall guard triggered.
- Layout: 1889 modules, layer/import/cycle/aggregate checks passed.
- Links: 944 Markdown files, 5793 local links, 111 fragments, no errors.
  The read-only link check required a sandbox retry because Node's `git`
  child process was restricted; the checker itself was unchanged.
- Retirement: 19 snapshot hashes verified, all 15 retired numerical modules
  absent from active imports.
- The five new source files contain no `sorry`, custom axiom,
  `native_decide`, `implemented_by` or raised proof limits. `git diff --check`
  passed. Root README and dependency pins are unchanged.

This verifies constructive diagram support and raw spanning. It does not
verify the still-open exclusion of invalid diagrams on arbitrary grouped
source vectors, or original endpoint 2.
