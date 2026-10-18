# Finite virtual SU(6) restricted characters

Environment-specific paths were normalized at stage 02; recorded outcomes are unchanged. Commands assume elan, lake and lean on PATH and execution from the repository root.

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1 + mathlib v4.33.1

- Reviewer/tool: Codex with Lean/Lake and mathlib
- Version: Lean 4.33.1, Lake 5.0.0, mathlib v4.33.1
- Scope: Finite virtual SU(6) restricted characters

### Claim checked

The restricted character of any finite integer-linear combination of actual
finite-dimensional SU(6) representations is invariant under the concrete
`(3 6)` Weyl action. If the actual summands are supplied with Laurent
polynomials in one common faithful, swap-compatible evaluator, then the finite
virtual combination has a faithful Laurent model and its polynomial is fixed by
`Flipped.swap36`.

### Result

- [x] confirmed
- [ ] counterexample found
- [x] proof gap found
- [x] assumption missing
- [ ] inconclusive

### Details

Kernel-checked in `GUT/SU6/Characters/VirtualRestriction.lean`:

- `FiniteVirtualSU6Representation.restrictedCharacter_swap36_fixed`
- `modeledFiniteVirtual_has_laurent_model`
- `ActualLaurentModelProvider`
- `FiniteVirtualSU6Representation.restrictedCharacter_has_faithful_swapCompatible_laurent_model`
- `VirtualLaurentModel.swap36_fixed`
- `modeledFiniteVirtual_poly_swap36_fixed`
- `modeledFiniteVirtual_poly_ne_flippedSMCharacter`
- `modeledFiniteVirtual_poly_ne_flippedSMCharacterExplicit`
- `FiniteVirtualSU6Representation.no_flippedSM_uplift_of_actual_provider`
- `FiniteVirtualSU6Representation.no_flippedSMExplicit_uplift_of_actual_provider`
- `AlgebraicTorusPoint.swap36_involutive`
- `Exp.eval_swap36Exp`
- `Poly.eval_zero`
- `Poly.eval_add`
- `Poly.eval_zscale`
- `Poly.eval_swap36`

The successful command was:

```text
lake build
```

with output:

```text
✔ [3247/3249] Built GUT.LaurentEvaluation
✔ [3248/3249] Built SU6NoGo
Build completed successfully (3249 jobs).
```

### Consequence

The finite-virtual closure step is formalized. The Laurent syntax also now has
a concrete algebraic-torus evaluator with checked swap compatibility. The
remaining gap is sharper: construct, from SU(6) torus weight theory, the common
faithful Laurent evaluator and the actual summand Laurent polynomials, and
connect that evaluator to the actual diagonal SU(6) torus points.

---
