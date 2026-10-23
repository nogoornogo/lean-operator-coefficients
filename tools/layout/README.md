# Source Layout Checks

The [source API migration](../../docs/topics/source-api-compatibility/migration-guide.md)
records canonical paths and protected aliases. After a complete rebuild, run:

```sh
python3 tools/layout/check-source-api.py
node tools/layout/check-math-namespaces.mjs
PYTHONDONTWRITEBYTECODE=1 python3 tools/layout/test-source-api.py
PYTHONDONTWRITEBYTECODE=1 python3 tools/layout/test-source-generators.py
PYTHONDONTWRITEBYTECODE=1 python3 tools/layout/test-audit-inventory.py
PYTHONDONTWRITEBYTECODE=1 python3 tools/layout/test-source-additions.py
```

`source-api-plan.py` freezes ownership and source checksums from a successful
branch build; `source-api-apply.py` is a one-time operation guarded by those
checksums. Do not regenerate the plan from partially rebuilt or other-branch
caches. `ExportSourceAPI.lean` exports the elaborated environment to the temporary
path selected by `SOURCE_API_EXPORT`. These inventories guide refactoring;
Lean consumer builds and strict alias/audit checks validate it. The older Math
namespace inventory additionally uses two recorded pre-baseline spellings in
`namespace-check-repairs.json`; both current declarations predate this refactor.
Private macro names normalize both dotted and compiler-encoded module paths.
`source_api_registry.py` combines that immutable plan with the bounded
shared-restriction addendum; it does not overwrite the original inventory.

The alias command in `Math.Lean.Compatibility` preserves old binder type heads
for field notation, constructor patterns and universe parameters. Computational
aliases inline their canonical values, including eliminators, rather than ask
the compiler to emit duplicate recursor implementations. The command checks
the exact canonical value, exact restoration of its type through direct legacy
aliases, and the unchanged three-axiom allowlist. Lean kernel-checks each alias
declaration. Generated facades use `compatibility_declarations`, followed by one
`assert_compatible` command per registered alias with the default budget; the
post-build checker rejects any missing individual check. Small controls can use
`compatibility_aliases` to construct and check the group together.

Run from the repository root:

```sh
node tools/layout/check-layout.mjs
node --test tools/layout/test-check-layout.mjs
```

The checker enforces Math -> no Physics/GUT, Physics -> no GUT, existence of
local imports, absence of import cycles, and coverage of every source/audit by
the `GUT.lean` aggregate. It uses source files, not stale compiled artifacts.
It is not a Lean parser or a proof checker; `lake build` remains mandatory.

`check-source-references.py` compares a saved pre-migration `.ilean` snapshot
with rebuilt canonical symbol references to detect unexpected name resolution.
It checks both reference sets and the source order of resolved occurrences.
The recorded six-quark proof split compares all unchanged definition and
statement references separately; its reviewed replacement proof remains subject
to the original strict audit. `check-source-transform.py` replays the frozen
migration and this repair in a temporary tree, detecting unregistered source
changes without writing repository sources or the Git index.
Recorded synchronous-elaboration insertions add only their option symbol to the
expected reference sets; all original declaration/proof references remain checked.
`check-audit-counts.py` compares the original and rebuilt build logs. Supply
`--baseline-constants` and `--rebuilt-constants` snapshots from `ExportSourceAPI.lean`
to verify the recorded compiler-helper count changes exactly. Their hashes,
helper categories, retained parents and protected names are checked against the
parent and proof-memory topic's `audit-inventory-repairs.json` records; the Lean
audit predicates/allowlists are unchanged. Multi-message inventories permit only
the recorded count at its exact position; every other count must match unchanged.
`test-source-generators.py` intercepts writes and checks generated paths,
imports and exact content against checked canonical sources.

`source-map.json` records the original relocation, not a permanent classification
by upstream project. The original relocation did not rename declarations;
the separate [Math namespace topic](../../docs/topics/math-namespaces/README.md)
now migrates Math-owned declarations, without changing historical module names.
`Math/Audit/ImportOrigin.lean` maps relocated modules back to their old identities
for the existing exclusion audits; the checker detects drift in that generated
table. The old predicates and axiom allowlists are unchanged.

New modules need no historical mapping, but must satisfy the layer rules and
be added to the relevant root import file. Moving a mapped module again requires
updating its map entry and regenerating ImportOrigin with the exported
`originSource` function. See [the layout](../../docs/architecture/MODULE_LAYOUT.md)
and [the migration record](../../docs/topics/math-physics-gut-layout/README.md).

## Namespace Migration Tools

`inventory-namespaces.mjs` reports explicit namespace openings from source.
`rename-math-namespaces.mjs` constructs an ownership-aware rename plan from a
fully built baseline's `.ilean` metadata; `--apply` freezes its declaration map
and applies mechanical changes. It deliberately refuses a second application
after the map exists: partially rebuilt metadata is not a baseline. These tools
are migration aids, not proof checkers. `update-namespace-docs.mjs` updates
current qualified references from the frozen map, excluding historical records
and the migration's old-name inventory. Full builds and unchanged audits remain
the acceptance criteria.

The mechanical plan is followed by source review and build-driven adjustments
for split namespace openings and imports that do not expose a shared namespace.
It is not an unattended general-purpose Lean renamer.

After rebuilding, `node tools/layout/check-math-namespaces.mjs` checks all frozen
old/new correspondences against rebuilt Math metadata and rejects Math-owned
legacy declarations. It does not establish theorem validity by itself.

The [proof memory audit](../../docs/topics/proof-memory-audit/README.md) adds exact
declaration-bounded proof-body replacements to source replay. The reference
comparison validates the recorded baseline ranges against frozen source, then
compares all remaining resolved references and occurrence order. It does not
require a replacement proof to use the same lemmas; theorem statements, exact
replacement text, kernel checks and unchanged strict axiom audits remain gates.
The same registry separately records exact module-local sequential-elaboration
insertions; their original proof references are still compared in full.

The [one-family structural cubature pilot](../../docs/topics/higgs-cubature-structure/README.md)
adds 140 exact proof-body rewrites and exact import/docstring preambles to the
same replay. Its six new library files have a checksum manifest and explicit
aggregate imports. The original 4,218 source paths still undergo exact replay;
the new files undergo separate source review, focused/full builds and a strict
module-owner inventory including private helpers. Source-declared additions are
reconciled as additions, separately from compiler helpers. Removed old public
names and additions from unrelated owners remain rejected. No axiom predicate,
layer restriction or allowlist changes. The foundation count uses its Math-only
import environment; six later Physics extensions of the same object namespace
remain in the global export but are absent from that audit environment.

The later SU(6) feasibility and shared-field children add 25 sources after that
frozen refactor. Their topic-owned
[SU(6) manifest](../../docs/topics/su6-protection-feasibility/source-additions.json)
and [field-connection manifest](../../docs/topics/model-input-connections/source-additions.json)
record each source checksum and its owning aggregate import. Source replay
checks these additions separately while preserving every older source/import
comparison. Extra, duplicate, missing or wrong-layer aggregate imports, changed
source hashes and replacement of a frozen source are rejected. These manifests
do not replace the topics' Lean builds or strict audits.

The resumed [remaining-family phase](../../docs/topics/higgs-cubature-structure/remaining-plan.md)
adds a second disjoint six-source manifest and 280 exact body replacements.
The frozen pilot source manifest and measurements retain their own checkpoint.
All 420 moment entry types are observed before and after the resumed rewrite;
`ExportHiggsCubatureTypes.lean` now imports all three families. The current
inventory reconciliation covers both source manifests while the original strict
Lean audits remain unchanged. The remaining-family comparison selects 82 exact
historical compiler records from the prior full-project audit and compares them
to a fresh candidate closure, including both structural additions and the first-collinear proof, which
is freshly compiled in the candidate. It explicitly reports this cross-run comparison and
never counts an ordinary `Replayed` result as a new baseline compilation.
