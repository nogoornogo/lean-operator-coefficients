# Full Vectorlike Spectrum Connection

- ID: vectorlike-spectrum
- Status: completed
- Checkpoint detail: completed. Started/completed: stage 01.
- Working branch: `proof/vectorlike-spectrum`.
- Integration target: `master`.

## Frozen Endpoint

From an actual SM x H equivalence K = K0 + X + X.dual, derive the
balanced-species certificates and actual exterior qque. K0 retains the
exact-spectrum source conditions; compact H and compatible continuous
actions remain. X is finite-dimensional and continuous. Duality includes H.
Do not replace the missing multiplicity duality by a new input certificate.

## Stages

1. Multiplicity direct sums, transport and duality. Prove the trace pairing
   on intertwiner spaces is perfect using existing semisimple splittings;
   construct the residual-equivariant duality. Commit the checked mathematics.
2. Assemble balanced-species certificates and the exterior connection. Commit
   after focused builds and strict audits.
3. Construct a nonzero-extra source/control with explicitly paired residual
   actions. No vacuum, Yukawa, anomaly or dynamics claims. Verify and commit.

No dependency updates or new foundational projects. If the trace-pairing
route fails, inspect the existing compact decomposition route once; preserve
checked milestones and report the missing interface instead of weakening
the endpoint. Do not merge an incomplete three-stage task.

## Verification

Each proof milestone needs focused/full builds and strict axiom/import audits.
Run layout/link/diff checks; reuse exterior computational controls at assembly.
Lean LSP MCP unavailable; use source reads and targeted Lean builds.

## Progress

Stage 1 (`checkpoint 01`) proved: the trace pairing is perfect for an irreducible constituent
and a semisimple first-factor representation. Its transpose construction gives
the H-equivariant equivalence M(X.dual,R.dual) = M(X,R).dual. Multiplicity
transport and product decompositions are also proved. This stage alone did
not yet supply the positivity/exterior endpoint.

Stage 1 verification: focused duality audit (8 strict axiom checks), full
`lake build` (5729 jobs), layout (684 modules), links (277 Markdown files,
1570 links), and `git diff --check` passed. Existing dependency warnings only.
No computational contraction changes in this mathematical stage.

Stage 2 (`checkpoint 02`) proved: the full SM x H decomposition now derives balanced species
certificates, shared positivity and the actual exterior endpoint. See
[interfaces and remaining boundary](results.md).

Stage 2 verification: focused assembly audit (5 strict axiom checks), full
`lake build` (5732 jobs), layout (687 modules), links (278 Markdown files,
1573 links), one-generation controls (4), pairwise controls (3), and diff
checks passed. No new warnings or changes to the trusted proof boundary.

Stage 3 proved: actual retained SU(5) matter plus a full matter/dual-matter
pair, with zero mass and trivial H. All global-decomposition and continuity
inputs are constructed. The additional Q multiplicity is positive; the
source is NOT any exact SM-plus-singlets spectrum, but shared positivity
and actual nonzero exterior qque hold. See [the statement](../../proof/current/inputs/Physics/VECTORLIKE_SPECTRUM.md).

Stage 3 verification: focused concrete-source audit (8 strict axiom checks),
full `lake build` (5734 jobs), layout (689 modules), links (279 Markdown
files, 1585 links), one-generation controls (4), pairwise controls (3), and
diff checks passed. Across the three audits, 21 named declarations passed
strict transitive axiom checks; only propext, Classical.choice and Quot.sound.
Existing dependency warnings remain, with no new source warnings or pin changes.

## Completion And Boundary

All three deliverables are proved, with staged commits. Integration target
remains master, by no-ff merge after final verification; Git ancestry is the
integration record. Retain the topic branch. No remote push.

The global SM x H spectrum equivalence is still supplied for arbitrary models;
only the concrete benchmark constructs it from its actual source. Neither
SM-only vectorlike counts nor arbitrary UV mass data suffice. The benchmark
uses trivial H and zero mass, not realistic Yukawa/vacuum or decay dynamics.
The general entrance retains compact continuous H without Abelianity.
