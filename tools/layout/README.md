# Source Layout Checks

Run from the repository root:

```sh
node tools/layout/check-layout.mjs
node --test tools/layout/test-check-layout.mjs
```

The checker enforces Math -> no Physics/GUT, Physics -> no GUT, existence of
local imports, absence of import cycles, and coverage of every source/audit by
the `GUT.lean` aggregate. It uses source files, not stale compiled artifacts.
It is not a Lean parser or a proof checker; `lake build` remains mandatory.

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
