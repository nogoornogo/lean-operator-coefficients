# Positive color coupling verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](colored-positive-coupling-results.md).

Focused builds are serialized with one Lean thread, a sampled 6 GiB
process-group RSS cap, 4 GiB host reserve and 300-second wall cap.
`RestrictedColorWordSupport` built successfully: 4112 jobs, guarded 4.5 s,
sampled peak 4890096 KiB. `ColorInternalPairExclusion`, including all actual
local certificates, built successfully: 4110 jobs, guarded 19.0 s, sampled
peak 4975784 KiB. These observations are build-resource measurements, not
mathematical inputs.

- Math structural strict transitive audit: 1726 declaration checks passed;
  guarded 6.0 s, sampled process-group peak 5400140 KiB.
- Physics structural strict transitive audit: 306 checks passed; cached
  replay 2.8 s, sampled peak 873960 KiB. Total: 2032 structural checks.
- Full default `lake build`: 7290 jobs including Math, Physics and GUT;
  success, zero warnings/errors. Guarded 8.8 s, sampled process-group peak
  6659828 KiB. The 10 GiB full-build cap, 4 GiB host reserve and 300 s wall
  guard did not trigger.
- Layout: 1904 modules; layers, imports, cycles and aggregate checks pass.
- Links: 947 Markdown files, 5834 local links, 111 fragments, zero errors.
- Retirement: 19 snapshot hashes checked; all 15 retired numerical modules
  remain absent from active imports.
- New/changed proof sources contain no `sorry`, custom axiom,
  `native_decide`, `implemented_by` or raised proof limits. Whitespace checks
  pass. Root README and dependency pins are unchanged.

During development a second guarded build was inadvertently started while
one dependency build was still running; it was immediately interrupted.
All subsequent focused, audit and full-build verification was serialized.
No memory guard triggered and no numerical certificate was evaluated or
reintroduced.

The topic overview was shortened to its current result and remaining task;
all 79 prior phase/interface links are retained in `phase-index.md`.
The full SM q/l consumer remains open; no complete endpoint-2 claim is made.
