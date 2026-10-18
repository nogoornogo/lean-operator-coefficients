# Concrete SU(6) Weyl representative for the (3 6) generator

Environment-specific paths were normalized at stage 02; recorded outcomes are unchanged. Commands assume elan, lake and lean on PATH and execution from the repository root.

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1 + mathlib v4.33.1

- Reviewer/tool: Codex with Lean/Lake and mathlib
- Version: Lean 4.33.1, Lake 5.0.0, mathlib v4.33.1
- Scope: Concrete SU(6) Weyl representative for the `(3 6)` generator

### Claim checked

There is a determinant-one unitary representative of the `(3 6)` transposition
whose conjugation action on diagonal maximal-torus coordinates is exactly the
modeled coordinate swap.

### Result

- [x] confirmed
- [ ] counterexample found
- [x] proof gap found
- [x] assumption missing
- [ ] inconclusive

### Details

Kernel-checked in `GUT/SU6/Characters/WeylMatrix.lean`:

- `signedSwap36_mem_specialUnitary`
- `signedSwap36SU_conj_diagonal`
- `signedSwap36SU_conj_diagonal_entry`

Kernel-checked in `GUT/SU6/ProtonStabilityNoGo/FlippedBranch/ConcreteBridge.lean`:

- `ambientPointOfDiag_swap36`
- `concrete_matrix_realizes_swap36WeylActionData`

The representative is the ordinary `(3 6)` permutation matrix multiplied by one
diagonal sign. The ordinary transposition has determinant `-1`; the extra sign
changes the determinant to `1`. The sign cancels when conjugating diagonal
matrices, so the diagonal entries are still permuted by `(3 6)`. The resulting
six diagonal entries are then repackaged as the `Flipped.AmbientPoint` used by
the Laurent-polynomial bridge.

The successful command was:

```text
lake build
```

with output:

```text
✔ [3244/3246] Built GUT.ConcreteBridge
✔ [3245/3246] Built SU6NoGo
Build completed successfully (3246 jobs).
```

### Consequence

The concrete Weyl-representative coordinate action for the obstructing
generator is now Lean-checked and connected to the abstract flipped-coordinate
action. What remains is to package the concrete matrix action with the
finite-dimensional SU(6) representation restriction theorem and to prove that
the Laurent-polynomial restriction model is faithful for the characters under
consideration.

---
