# Compact Residual Group API Audit

Subsequent implementation: [compact light qque](../compact-light-qque/README.md)
closes the consumer connections identified here. This record retains the
audit's original endpoint and verification baseline.

- ID: compact-residual-api
- Status: completed
- Checkpoint detail: completed (bounded API audit; compact physical endpoint remains open).
- Result type: bounded feasibility audit, not a compact non-Abelian no-go theorem.
- Working branch: `audit/compact-residual-api`.
- Integration target: `master`.

## Endpoint

Check whether the pinned libraries can replace the finite-group character
counting and splitting steps used by the four-weight non-Abelian qque route.
Produce compiling connection probes, strict transitive axiom checks, and an
explicit map of remaining consumer obligations. Do not implement the entire
compact light-spectrum theorem in this audit.

## Frozen Inputs And Routes

Finite-dimensional complex normed representations; a compact topological group
with its Borel measurable structure; continuous group action. Operator-valued
continuity must be derived from the repository's joint-continuity predicate,
not silently inferred from the name `ContRepresentation`.

1. Preferred: TauCeti Haar character integral counts continuous intertwiners;
   identify these with algebraic intertwiners and test character additivity.
2. Only if needed: compact character orthogonality and isotypic projections.

Check semisimple splitting separately from character integration. The existing
unitary complete-reducibility theorem is available for arbitrary groups; do not
assume that compactness alone makes an arbitrary discontinuous action unitary.

## Stop Gate

One pass over these two routes. Stop at an API feasibility decision or a named
missing interface; no new Haar/Peter-Weyl foundations or dependency upgrades.
No changes to the E6 literature boundary, full-SM/Lorentz/Grassmann operator
scope, Wilson coefficients, or existing finite-group statements.

## Deliverables

- Algebraic/continuous representation and Hom-dimension adapters.
- A persistent axiom audit and an infinite-group specialization.
- Splitting/continuity dependency map and bounded next implementation step.
- Focused/full builds, layout/link checks, commit and integration.

## Verification

See [connection assessment](results.md) for the checked interfaces and exact
remaining consumer obligations. The preferred route suffices; the alternative
projector route is not needed.

Verified stage 01:

- `lake build Math.RepresentationTheory.Characters.Audit.AuditCompactResidualAPI`:
  passed (3796 jobs), 14 strict transitive axiom checks. Only `propext`,
  `Classical.choice`, `Quot.sound` permitted; import boundary checked.
- `lake build`: passed (5639 jobs).
- `node tools/layout/check-layout.mjs`: 602 modules, passed.
- `node tools/docs/check-links.mjs`: 246 Markdown files, 1336 local links,
  32 heading fragments, zero errors.
- `git diff --check`: passed. No dependency pins or existing endpoint changed.
- Existing linter warnings are replayed by the build; the three new Lean
  files introduce no warnings. No new axiom exceptions or literature inputs.

Lean LSP MCP is unavailable in this session; source inspection and focused
`lake build` checks were used instead.

## Result And Next Boundary

The direct Haar/Hom-dimension route is viable. Reusable character-counting and
semisimple-splitting adapters are proved; an infinite compact specialization
and compact unitarization are audited. The five consumer obligations in
[results](results.md) define the next bounded implementation, not continuation
of this audit. In particular, finite-group removal from the physical theorem
is **not** marked complete.

Integration target remains `master`; Git ancestry records integration. Retain
the audit branch. No remote push is requested.
