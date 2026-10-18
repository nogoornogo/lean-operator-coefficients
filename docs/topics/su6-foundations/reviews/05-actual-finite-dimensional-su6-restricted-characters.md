# Actual finite-dimensional SU(6) restricted characters

Environment-specific paths were normalized at stage 02; recorded outcomes are unchanged. Commands assume elan, lake and lean on PATH and execution from the repository root.

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1 + mathlib v4.33.1

- Reviewer/tool: Codex with Lean/Lake and mathlib
- Version: Lean 4.33.1, Lake 5.0.0, mathlib v4.33.1
- Scope: Actual finite-dimensional SU(6) restricted characters

### Claim checked

The restricted character of an actual finite-dimensional complex representation
of `Matrix.specialUnitaryGroup (Fin 6) ℂ` is invariant under the concrete
`(3 6)` Weyl action on diagonal SU(6) torus points. Any faithful,
swap-compatible Laurent-polynomial model of such a restricted character is
therefore fixed by `Flipped.swap36`.

### Result

- [x] confirmed
- [ ] counterexample found
- [x] proof gap found
- [x] assumption missing
- [ ] inconclusive

### Details

Kernel-checked in `GUT/SU6/Characters/ActualRestriction.lean`:

- `restrictedCharacter_swap36_fixed`
- `restrictedCharacter_swap36_fixed_via_bridge`
- `LaurentRestrictedCharacterModel.swap36_fixed`
- `LaurentRestrictedCharacterModel.poly_ne_flippedSMCharacter`
- `LaurentRestrictedCharacterModel.poly_ne_flippedSMCharacterExplicit`

The successful command was:

```text
lake build
```

with output:

```text
✔ [3245/3247] Built GUT.ActualRestriction
✔ [3246/3247] Built SU6NoGo
Build completed successfully (3247 jobs).
```

### Consequence

For actual finite-dimensional SU(6) representations, the Weyl-invariance part
of the bridge is now formalized. The remaining proof gap is no longer
conjugacy-invariance or the concrete Weyl representative; it is the
representation-ring/Laurent-model theorem asserting that restricted finite
virtual SU(6) characters always admit the faithful, swap-compatible Laurent
model used here.

---
