# Staged readability review and replacement plan

## Acceptance criteria

For each targeted certificate, explain the mathematical objects, coordinate
ordering, defining operations and the reason for independence/spanning or
separation. Link the paper expression to its independently defined semantic
carrier. State explicitly which obligations are structural and which remain
finite computation. Preserve both directions of existing equivalences and all
actual-field, exchange, residual-action and flavor-boundary consumers.

A successful structural replacement removes the opaque table or closed
certificate from the relevant theorem's dependency chain. A readable derivation
that still requires a finite calculation is a partial improvement, not a claim
that numerical proof has been eliminated. Retain prior proofs until replacements
and downstream verification pass; never archive an indispensable proof first.

## Phase 1 — Dependency and explanation map

Inspect only the existing topic's linked sources initially. For
`LiSixQuarkFiniteData`, map each table and theorem to its consumers: seed
coordinates, selected exchange words, basis matrix, inverse matrix, coordinate
agreement and the eventual basis/printed-span results. Separate generated
proposal data from semantic definitions and proof obligations. Record exact
paths and declarations, not just tactic counts.

Produce a short explanation of what a row and column mean, how coefficients
arise from epsilon contractions and fermionic exchanges, and where the extra
alternating-down component enters. Check the existing 24-dimensional printed
span and 25-dimensional extended-space results before choosing a decomposition.
Do not assume those dimensions already provide an independent replacement:
their proofs may depend on the very matrix being replaced.

Stop this phase with a dependency map, circularity check and a bounded proposal.

## Phase 2 — One structural Li pilot

Try a small, semantically meaningful subspace or exchange relation first.
Prefer symbolic exchange relations, explicit invariant-subspace decompositions,
triangular/block coordinate maps and reconstruction lemmas over a dense inverse.
Present the derivation in a companion topic document and readable named lemmas.
Show that the pilot agrees with the existing literal contractions and conventions.

Freeze the pilot statement and existing interfaces before coding. A pilot must
explain a genuine independence/spanning step, not merely prove another concrete
matrix entry. If it requires substantial new representation theory unavailable
in the pinned dependencies, stop with the precise missing interface and options.
Do not silently start that foundational project.

## Phase 3 — Li replacement and downstream preservation

Only after a successful pilot, extend the approach to the full selected space.
Derive the basis and reconstruction structurally where feasible; isolate and
explain any irreducible small coordinate checks. Remove dense inverse data from
active proof premises only after the new derivation supplies all consumers.
Recheck the printed-span kernel, down-flavor boundary, typed exchange equations,
residual Hom transport and nonzero actual-field witnesses. Keep statements and
physical interpretation unchanged. Document any remaining computational core.

## Phase 4 — Other certificate families

Use the same review rubric, in this provisional order:

1. Heeck–Le six-quark data: reuse justified Li structures and exchange derivations.
2. SU(6) finite-index certificate: seek interpretable charge/index identities
   explaining annihilation and target separation.
3. Exact-rank examples: derive small examples by explicit row/column relations;
   keep the general rank-certificate API distinct from its numerical examples.
4. E6 finite Lie certificates: assess root/weight/block structure and provenance;
   do not promise a table-free E6 construction without a feasibility decision.

Freeze an endpoint and stop conditions for each family before implementation.
Finite SM assignment counts and individual arithmetic witnesses form a separate
review category; they are not silently included in this first replacement.

## Resource and verification gates

Keep Lean and dependency pins unchanged. Use no custom axioms, `sorry`,
`native_decide`, audit exceptions or raised proof limits. Do not rebuild retired
numerical modules. Use focused checks before a serialized full default build.
For an expensive check, use `tools/exact-rank/kernel-probe.py` with one Lean
thread, a 10 GiB sampled process-group guard, a 4 GiB host-memory reserve and
300 seconds per invocation. A guard stop is not a failed theorem or permission
to increase the budget; revise the proof structure or record a bounded stop.

For each implemented milestone: focused builds, persistent strict transitive
axiom audits, layout checks, local-link checks and whitespace checks. Before
claiming an integrated replacement, run the full build and verify downstream
consumers. Record commands and residual limits in the topic. Stop on a changed
mathematical statement, new physical premise, new foundation or unresolved
semantic mismatch requiring a scope decision. No merge or push is authorized.
