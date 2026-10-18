# Joint Species Connection

## Frozen Endpoint

For the unchanged zero-mass Georgi-Glashow source and arbitrary ordinary
unitary centralizer action R, restrict the already constructed exchange to
the canonical full Q/up/e evaluation images in the radical and its dual.
Derive SM x H invariance, nonzero exterior descent for n > 0, and the
corresponding nonzero residual Hom via the existing completeness equivalence.
Prove reconstruction of this specific coefficient, not merely existence of
another allowed coefficient. Keep g != 0 and v != 0 unchanged.

Route: generation-wise SM intertwiners; finite-dimensional exhaustion of
canonical evaluation images; restriction of the previous actual currents.
Derive SM invariance by expanding over generations and using the original
SU(5) contraction. H invariance follows from the previous ambient theorem.
No H-stability assumption on an individual generation, no compactness or
continuity hypothesis on H, no assumed coefficient equality or nonzero map.

Required finite interfaces: generation embeddings and dual projections,
full-image exhaustion, joint invariance, exterior probe, completeness
reconstruction. No new vacuum, mass selection, UV action, SUN application,
amplitude or foundational library. No pin, axiom or heartbeat changes.
Stop if this route needs a separate mathematical foundation and record the
precise unsolved obligation; do not change hypotheses to bypass it.

## Verification

- `lake build GUT.SU5.Audit.AuditLightSpeciesCompleteness
  Math.LinearAlgebra.Audit.AuditFourSlotGeneration
  Physics.StandardModel.Operators.Audit.AuditMediatorQqueEvaluation`: passed.
  Strict transitive axiom checks: 40 + 1 + 3, allowing only `propext`,
  `Classical.choice`, `Quot.sound` (42 new checks, two existing checks rerun).
- Full `lake build`: passed, 5833 jobs. Existing warnings replayed; no new
  source warnings. No heartbeat or dependency-pin changes.
- Exact computational regressions: `python3 tools/qque/audit_one_generation.py`
  (4), `python3 tools/qque/audit_pairwise.py` (3),
  `python3 tools/qque/audit_contraction_uniqueness.py` (3): all passed.
- `node tools/layout/check-layout.mjs`: passed, 782 modules.
- `node tools/docs/check-links.mjs`: passed, 295 Markdown files, 1775 local
  links, 33 heading fragments.
- `git diff --check`: passed. Lean LSP unavailable; used focused builds.

Commit on `proof/light-matching-coherence` and integrate with no-ff into
`master`; rerun the full build and consistency checks on the merged state.
Git ancestry records integration. Retain the topic branch; no remote push.

## Construction

[LightSpeciesMaps](../../../GUT/SU5/Matching/LightSpeciesMaps.lean) gives explicit
SM intertwiners from every generation into the same radical and dual used in
the first phase. The canonical full-species evaluation images are stable
under SM x H without choosing a flavor basis for H. Joint continuity of the
SM restriction is derived from the known gauge action and the actual radical
equivalence; this supplies semisimplicity without any topology on H.

[LightSpeciesExhaustion](../../../GUT/SU5/Matching/LightSpeciesExhaustion.lean)
constructs all-generation sum maps and left inverses. Their injectivity and
the already proved exact SM multiplicity dimensions give surjectivity onto
the canonical Q/up/e images. These are full species, not selected H
constituents or separately postulated field decompositions.

[LightSpeciesExchange](../../../GUT/SU5/Matching/LightSpeciesExchange.lean)
restricts the original radical currents using the subspace inclusions. It
derives, for generation indices a,b,c,d, the ordered coefficient

```text
C(Q_a(q), Q_b(s), U_c(u), E_d(e))
  = delta(a,c) delta(b,d) C_SU5(q,s,u,e).
```

SM invariance extends from these generators to all species via the generic
[four-slot finite-generation lemma](../../../Math/LinearAlgebra/FourSlotGeneration.lean).
H invariance follows from the earlier actual-radical currents, with explicit
identities for the restricted primal and dual actions. Product-group
invariance combines these two results on the same coefficient.

[LightSpeciesCompleteness](../../../GUT/SU5/Matching/LightSpeciesCompleteness.lean)
defines the generated element in `FullLightSpeciesQque.Sector` and its
`ResidualHom` coordinate via the existing equivalence. `coefficient_restrict`
identifies the ordered coefficient with the previous actual-radical exchange;
`generated` is its alternating descent through the existing `MediatorQque`
construction, not an independently chosen allowed functional. An explicit
spinor probe proves nonzero descent, and `reconstruct` recovers this same
generated element from its Hom coordinate. The shared
[evaluation API](../../../Physics/StandardModel/Operators/MediatorQqueEvaluation.lean)
transfers a nonzero alternating probe along a proved ordered-coefficient
restriction. The SU(5) application proves both that restriction and the probe;
neither becomes a new model premise. One- and three-generation controls retain
arbitrary H and R.

A direct equality between the two differently typed ambient exterior
functionals was not added. The
connection is instead the proved ordered restriction followed by the existing
alternation construction and its slot-evaluation theorem. Model-independent
evaluation lemmas avoid repeating large concrete carrier expressions. No
heartbeat increase is used.

The final module excludes the `LightSpeciesCompleteness` namespace from
Lean's automatic premise-selection search index. A debugger trace localized
the export-time slowdown to `LibrarySuggestions` / `FunInfo.collectDeps`,
not kernel checking. This narrow search-metadata setting leaves the theorem
statements, explicit theorem applications, kernel checks and strict axiom
audits unchanged. With it, the final module built in 3.9 seconds; no dependency
pin or axiom-audit policy was changed. Trial builds before this adjustment
were interrupted, not counted as verification successes.

## Scope

H remains an arbitrary abstract group with the existing ordinary unitary
centralizer action. No individual generation is declared H-stable. No
independent nonzero or invariant coefficient hypothesis is introduced.
Positive generation count and nonzero g,v remain necessary endpoint inputs.

This closes a connection for the specified zero-mass SU(5) fermion source
and the retained ten-sector exchange convention. It does not derive a
nonzero-mass spectrum from a vacuum, reconstruct all UV interactions, or
automatically furnish SUN/Spin/E6 light-species matching. It is not a physical
amplitude or decay-width theorem.
