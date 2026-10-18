# Selection Rules Module Paths

- ID: selection-rules-paths
- Status: completed
- Result type: module relocation
- Working branch: `refactor/selection-rules-paths`
- Integration target: `docs/documentation-review`
- Parent exception: bounded child of the unmerged documentation review.

## Endpoint

Rename the existing model application directories `ProtonStabilityNoGo` to
`SelectionRules`, update imports and documentation, and preserve declaration
names and historical import exclusions. No theorem hypotheses or dependency
pins change. More detailed subject redistribution is outside this mechanical
rename.

## Verification

Focused build of Spin(10) half-spin, SU(5) charge-profile, SU(6) standard
branching and scoped no-go audits: 4,547 jobs passed, including their strict
transitive axiom and import-boundary checks.
Standalone `lake build`: 6,253 jobs passed, zero warnings/errors.
No master merge is authorized.

## Implementation

Moved 132 modules across SU(5), SU(6), Spin(10), E6 and SU(N). Updated
aggregates, consumers and current documentation. Historical narrative paths
remain checkpoint records; live Markdown links resolve to current files.
`tools/layout/source-map.json` and generated `Math/Audit/ImportOrigin.lean`
preserve the original names used by import-boundary audits.

The staged Lean diff, excluding the generated identity helper, contains only
import updates and executable-command path comments (656 changed lines).
Declaration namespaces, proof bodies, axiom allowlists and dependency pins
are unchanged.

Layout check: 1,015 modules passed. Link check: 376 Markdown files, 2,552
links, 94 fragments, zero errors. Layout tests and diff checks passed.

The first full build overlapped with the focused build and encountered a
missing generated `.olean` while the other process built that same target.
The subsequent standalone full build passed after both processes ended;
the intermediate failure is not treated as a successful build.

The bounded rename is complete and awaits integration into its recorded parent.
