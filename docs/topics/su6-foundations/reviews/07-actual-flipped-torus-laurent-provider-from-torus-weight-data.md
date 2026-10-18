# Actual flipped-torus Laurent provider from torus weight data

Environment-specific paths were normalized at stage 02; recorded outcomes are unchanged. Commands assume elan, lake and lean on PATH and execution from the repository root.

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1 + mathlib v4.33.1

- Reviewer/tool: Codex with Lean/Lake and mathlib
- Version: Lean 4.33.1, Lake 5.0.0, mathlib v4.33.1
- Scope: Actual flipped-torus Laurent provider from torus weight data

### Claim checked

From the actual flipped diagonal SU(6) subtorus and a finite torus eigenbasis
certificate for each actual representation, the restricted trace character is
represented by the common algebraic Laurent evaluator. Consequently this
eigenbasis-level weight theory constructs the `ActualLaurentModelProvider`
needed by the finite-virtual obstruction.

### Result

- [x] confirmed
- [ ] counterexample found
- [x] proof gap found
- [x] assumption missing
- [ ] inconclusive

### Details

Kernel-checked in `GUT/SU6/ProtonStabilityNoGo/FlippedBranch/FlippedTorus.lean`:

- `FlippedDiagonalSU6Point.det_product`
- `FlippedDiagonalSU6Point.coord_ne_zero`
- `FlippedDiagonalSU6Point.coord5_eq_inv_colorProduct`
- `FlippedDiagonalSU6Point.coordUnit5_eq_z6`
- `FlippedDiagonalSU6Point.toAlgebraicTorusPoint_swap36`
- `FlippedDiagonalSU6Point.restrictedCharacter_swap36_fixed`

Kernel-checked in `GUT/SU6/Characters/LaurentEvaluation.lean` and
`GUT/SU6/Characters/WeightTheory.lean`:

- `RawCharacter.eval_toPoly`
- `RawCharacter.eval_mapWeights_one`
- `WeightTheory.commonLaurentEvaluatorOfFaithful`
- `WeightTheory.trace_eq_sum_of_basis_eigen`
- `WeightTheory.rawCharacterOfWeights_eval`
- `WeightTheory.TorusEigenbasis.restrictedCharacter_eq_sum`
- `WeightTheory.TorusEigenbasis.toActualTorusWeightCharacter`
- `WeightTheory.torusWeightTheoryOfEigenbasisTheory`
- `WeightTheory.actualLaurentModelProviderOfEigenbasisTheory`
- `WeightTheory.finiteVirtual_has_laurent_model_of_eigenbasisTheory`
- `WeightTheory.no_flippedSM_uplift_of_eigenbasisTheory`
- `WeightTheory.no_flippedSMExplicit_uplift_of_eigenbasisTheory`

The successful command was:

```text
lake build
```

with output:

```text
✔ [3249/3251] Built GUT.WeightTheory
✔ [3250/3251] Built SU6NoGo
Build completed successfully (3251 jobs).
```

### Consequence

The provider construction is now formalized down to a standard finite
eigenbasis trace computation: basis vectors transform by Laurent monomial
weights on the actual flipped diagonal subtorus, and Lean proves the trace is
the sum of those monomials. The remaining assumptions are (1) faithfulness of
the Laurent evaluator on a normalized or quotiented Laurent model and (2) the
existence of the torus eigenbasis theorem for the intended continuous/smooth
or algebraic finite-dimensional SU(6) representations.

---
