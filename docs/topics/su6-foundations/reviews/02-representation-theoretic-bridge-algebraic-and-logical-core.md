# Representation-theoretic bridge, algebraic and logical core

Environment-specific paths were normalized at stage 02; recorded outcomes are unchanged. Commands assume elan, lake and lean on PATH and execution from the repository root.

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Reviewer/tool: Codex with Lean/Lake
- Version: Lean 4.33.1, Lake 5.0.0
- Scope: Representation-theoretic bridge, algebraic and logical core

### Claim checked

If an ambient character is fixed by the ambient Weyl transposition `(3 6)`,
then its restriction to a subtorus preserved by that transposition is fixed by
the induced subtorus action. For the flipped SU(6) subtorus, the ambient
rank-5 exponent-lattice action for `(3 6)` commutes with the restriction map to
the rank-4 flipped lattice.

### Result

- [x] confirmed
- [ ] counterexample found
- [x] proof gap found
- [x] assumption missing
- [ ] inconclusive

### Details

Kernel-checked in `GUT/SU6/ProtonStabilityNoGo/FlippedBranch/Flipped.lean`:

- `AmbientExp.restrict_swap36`
- `AmbientExp.swap36_involutive`
- `WeylInvariantCharacter.restricted_swap36_fixed`
- `AmbientPoint.swap36_involutive`
- `FixedByConjugation.restricted_fixed_by_weyl_action`

The successful command was:

```text
lake build
```

with output:

```text
✔ [2/4] Built GUT.Flipped
✔ [3/4] Built SU6NoGo
Build completed successfully (4 jobs).
```

This removes the previous opaque assumption that restriction automatically
inherits the relative Weyl symmetry. It also kernel-checks the standard logical
route from conjugacy-invariance to Weyl-invariance. What remains outside Lean is
the trace/representation-theoretic input that finite-dimensional SU(6)
representation characters are conjugacy-invariant, the existence/action of the
relevant Weyl representatives, and the faithful identification of those
characters with the Laurent-polynomial model used here.

### Consequence

The bridge is now reduced to standard SU(6) character theory rather than the
specific flipped obstruction. The full no-uplift result is still conditional on
formalizing or importing that standard character-theory input.

---
