# Math Declaration Namespace Alignment

- ID: `math-namespaces`
- Status: completed
- Result type: refactoring
- Working branch: `refactor/math-namespaces`
- Integration target: `master`
- Integration evidence: user-authorized master integration; Git ancestry is authoritative

## Frozen Scope

Inventory namespaces defined by repository Math modules and their users across
Math, Physics, GUT, persistent audits and documentation. Rename Math-owned
`GUT.*` declarations to `Math.*`; retain external-library namespaces, source
paths, imports, mathematical statements, hypotheses and dependency pins.
Do not blindly replace all `GUT.*` references: Physics/GUT-owned declarations
remain distinct. Shared or reopened namespaces must be resolved by ownership.
Old declaration names need not be retained as compatibility aliases within
this repository; external API breakage must be documented.

## Plan And Acceptance

1. Create a checked-in ownership inventory and old/new correspondence table;
   identify shared namespace reopenings and potential collisions.
2. Apply ownership-aware changes to definitions and all consumers in coherent
   batches. Update current documentation and explicitly label historical names.
3. Run focused builds and strict transitive audits, then serialized full
   `lake build`, source layout, link and diff checks. Do not weaken audits.
4. Record the verified endpoint and commit; do not merge without user direction.

## Progress

The preceding documentation review was merged at `checkpoint 01`; its merged-state
link check and 14 documentation/layout tests passed. The former topic branch
was safely deleted. The [explicit-opening inventory](namespace-inventory.md)
records 487 Math files, 430 with legacy GUT openings and 323 distinct explicit
legacy namespace names. It is a lexical starting inventory, not yet an
elaborated declaration ownership map.

The [declaration map](declaration-map.json) freezes 4,227 old/new names from
the checked baseline's elaborated declaration and reference metadata. Generated
and private references are included. Shared namespaces are split by defining
module: Math declarations move, while Physics/GUT declarations remain in place.
Imports and the historical module-identity audit remain unchanged. Source and
consumer changes have been applied and verified; see [results](results.md).
No compatibility aliases are introduced: external callers must update names.

## References

- [Layout](../../architecture/MODULE_LAYOUT.md).
- [Workflow](../../architecture/WORKFLOW.md).
- [Math library](../../../Math/README.md).
