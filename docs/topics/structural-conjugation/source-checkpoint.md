# SC-1: Actual Conjugations To Profiles

Status: Lean-checked. This is the source-character bridge, not yet the
mass-radical endpoint or the concrete standard-chain adapter.

[ConjugationSource.lean](../../../Physics/StandardModel/Spectrum/ConjugationSource.lean)
uses namespace `GUT.StructuralConjugation` and imports no GUT application.

- `Realizes j p` contains an actual element and its conjugation identity on
  every torus point. `ThreeConjugations j` contains only the three such witnesses.
- `inclusion_conjugate` proves the ambient product-group identity, fixing the
  residual factor. `character_invariant` and `dual_character_invariant` derive
  trace invariance using the existing Math API.
- `target_invariant` uses faithful evaluation to derive invariance for a single
  chosen permutation. No full source Laurent model is needed.
- `coefficient_eq_of_invariant` and `profiles_equal_of_three_invariances`
  extract precisely the three coefficient/profile equalities.
- `orbitCompatible_of_three_invariances` applies those equalities to the exact
  dual SM target, including singlets and arbitrary additive Abelian labels.
- `profiles_compatible` composes the bridge for arbitrary actual finite-dimensional
  representations of `G x H`. The evaluated **source** dual target is its premise;
  SC-2 must derive that premise from the mass radical's target.

No mass invariance under the conjugating elements, radical invariance, full
Weyl invariance, profile compatibility or operator support is an input.
Continuity/unitarity are not needed for this trace bridge; actual nonnegative
spectrum and mass consumers introduce their declared additional assumptions.

## Verification

```sh
lake build Physics.StandardModel.Spectrum.Audit.AuditConjugationSource
lake build
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
git diff --check
```

Focused build: 3711 jobs, 10 strict transitive axiom checks passed, allowing only
`propext`, `Classical.choice`, `Quot.sound`. Full build: 5558 jobs. Layout: 542
modules, no errors. Documentation link and diff checks passed before commit.
New Lean files have no warnings; pre-existing warnings are unchanged.

The persistent [audit](../../../Physics/StandardModel/Spectrum/Audit/AuditConjugationSource.lean)
checks the actual consumer types, finite `ZMod 3` labels, and the residual-fixed
conjugation equation. A degenerate torus map checks that no injectivity or
order-two premise is hidden in the structure; it is not a physical non-vacuity
example. The concrete positive and negative controls remain SC-3/4 obligations.

No previous proof, dependency pin or audit allowlist was changed. No new
physical model class or novelty claim follows from this checkpoint alone.
