# Finsupp-normalized Laurent model and normalized virtual bridge

Environment-specific paths were normalized at stage 02; recorded outcomes are unchanged. Commands assume elan, lake and lean on PATH and execution from the repository root.

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1 + mathlib v4.33.1

- Reviewer/tool: Codex with Lean/Lake and mathlib
- Version: Lean 4.33.1, Lake 5.0.0, mathlib v4.33.1
- Scope: Finsupp-normalized Laurent model and normalized virtual bridge

### Claim checked

The exposed list Laurent syntax can be replaced by the normalized finitely
supported exponent model `Exp →₀ ℤ`, and the evaluator on this model is
faithful on both the algebraic torus and the actual flipped diagonal SU(6)
subtorus.  The finite-virtual no-uplift bridge can then be rebuilt on this
normalized model.

### Result

- [x] confirmed
- [ ] counterexample found
- [x] proof gap found
- [x] assumption missing
- [ ] inconclusive

### Details

Kernel-checked in `GUT/SU6/Characters/NormalizedLaurent.lean`:

- `Flipped.Normalized.Poly`
- `Flipped.Exp.evalVecMonoidHom_injective`
- `Flipped.Exp.linearIndependent_evalVecMonoidHom`
- `Flipped.Normalized.evalVec_faithful`
- `Flipped.Normalized.eval_faithful`
- `Flipped.Normalized.evalUnitAddTorus_faithful`
- `Flipped.Normalized.eval_zero`
- `Flipped.Normalized.eval_add`
- `Flipped.Normalized.eval_zscale`
- `Flipped.Normalized.eval_swap36`
- `Flipped.Normalized.eval_ofRawCharacter`
- `Flipped.Normalized.swap36_flippedSMCharacter_ne`
- `FlippedTorus.FlippedDiagonalSU6Point.ofUnitAddTorus`
- `FlippedTorus.FlippedDiagonalSU6Point.toAlgebraicTorusPoint_ofUnitAddTorus`
- `NormalizedVirtualRestriction.diagonalLaurentFaithful`
- `NormalizedVirtualRestriction.commonLaurentEvaluatorOfFaithful`
- `NormalizedVirtualRestriction.commonLaurentEvaluator`
- `NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider_evaluates`
- `NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider_swap36_fixed`
- `NormalizedVirtualRestriction.FiniteVirtualSU6Representation.no_flippedSM_uplift_of_actual_provider`
- `WeightTheory.PhysicallyAdmissibleSU6Representation`
- `WeightTheory.TorusEigenbasis.toActualNormalizedTorusWeightCharacter`
- `WeightTheory.actualNormalizedLaurentModelProviderOfEigenbasisTheory`
- `WeightTheory.finiteVirtual_normalized_poly_swap36_fixed_of_eigenbasisTheory`
- `WeightTheory.no_flippedSM_normalized_uplift_of_eigenbasisTheory`
- `WeightTheory.actualNormalizedLaurentModelProvider`
- `WeightTheory.finiteVirtual_normalized_poly_swap36_fixed`
- `WeightTheory.no_flippedSM_normalized_uplift`

The successful command was:

```text
lake build
```

with output:

```text
✔ [3640/3642] Built GUT.NormalizedLaurent
✔ [3641/3642] Built SU6NoGo
Build completed successfully (3642 jobs).
```

### Consequence

The list-syntax faithfulness problem is removed: Lean now proves faithfulness
in the canonical `Finsupp` model using linear independence of monomial
characters, then transfers the unit-torus version to the actual flipped
diagonal SU(6) subtorus by constructing the required diagonal SU(6) point.  The
intended representation class is now explicit as representations equipped with
a torus eigenbasis certificate; proving that all intended continuous/smooth or
algebraic finite SU(6) representations supply such a certificate remains the
next standard representation-theory bridge.

---
