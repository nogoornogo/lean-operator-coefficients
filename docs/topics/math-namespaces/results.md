# Namespace Migration Results

## Endpoint

Math-owned declarations formerly under `GUT.*` now use `Math.*`. The frozen
[map](declaration-map.json) contains 4,227 declaration/reference names, including
private and generated names, with their defining modules. This is distinct from
the lexical inventory's 323 explicit namespace openings. All 487 Math modules
were checked after rebuilding; no legacy Math-owned declarations remain.

Shared namespaces were split by ownership, not by spelling. Existing names in
730 Physics/GUT modules were compared with their pre-migration metadata: all
10,136 recorded declarations remain present under their original names.
Imports, source placement, mathematical hypotheses, dependency pins, historical
module exclusion predicates and axiom allowlists are unchanged.

## Verification

- `lake build Math`: successful, 5,793 jobs.
- `lake build`: successful, 6,547 jobs; no warnings or errors in the successful
  final run. Existing persistent strict transitive axiom audits were rebuilt.
- `node tools/layout/check-math-namespaces.mjs`: all 4,227 correspondences
  verified against rebuilt metadata; no legacy Math-owned declarations.
- `node tools/layout/check-layout.mjs`: 1,220 modules; layers, imports, cycles,
  aggregate coverage and historical relocation audit correspondence passed.
- `node tools/docs/check-links.mjs`: 495 Markdown files, 3,299 local inline
  links and 85 heading fragments; zero errors.
- `node --test tools/docs/test-check-links.mjs tools/layout/test-check-layout.mjs`:
  14 tests passed.
- Syntax checks for the migration/check scripts and `git diff --check`: passed.

Initial builds exposed declaration/module-name quoting distinctions, unnecessary
namespace opens, split namespace openings, and one ambiguous short `Group`
reference. These were corrected by preserving module identities, removing
unneeded opens and making the intended Math references explicit. No proofs were
replaced by assumptions and no audits were relaxed. Metadata tools aid the
refactor; successful Lean builds and the persistent audits establish acceptance.

## Compatibility And Integration

This changes the declaration-name API. No aliases for old Math-owned names are
provided. External users should use the map to update qualified names. Module
import paths are unchanged. Historical records retain checkpoint names and link
to the correspondence map rather than being rewritten as current results.

The topic is complete on `refactor/math-namespaces`. The user authorized master
integration; Git ancestry records the actual merge. The local topic branch is
deleted after successful merged-state verification.
