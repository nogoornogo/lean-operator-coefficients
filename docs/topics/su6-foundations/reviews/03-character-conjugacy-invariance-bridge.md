# Character conjugacy-invariance bridge

Environment-specific paths were normalized at stage 02; recorded outcomes are unchanged. Commands assume elan, lake and lean on PATH and execution from the repository root.

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1 + mathlib v4.33.1

- Reviewer/tool: Codex with Lean/Lake and mathlib
- Version: Lean 4.33.1, Lake 5.0.0, mathlib v4.33.1
- Scope: Character conjugacy-invariance bridge

### Claim checked

Finite-dimensional representation characters are invariant under conjugation.

### Result

- [x] confirmed
- [ ] counterexample found
- [x] proof gap found
- [x] assumption missing
- [ ] inconclusive

### Details

Kernel-checked in `Math/RepresentationTheory/Decomposition/MathlibBridge.lean`:

- `representation_character_conj`
- `su6_representation_character_conj`

This theorem imports `Mathlib.RepresentationTheory.Character` and applies
mathlib's `Representation.char_conj` theorem:

```text
ρ.character (h * g * h⁻¹) = ρ.character g
```

for an arbitrary group `G`, field `k`, finite-dimensional `k`-module `V`, and
representation `ρ : Representation k G V`. It is also specialized to
`Matrix.specialUnitaryGroup (Fin 6) ℂ`, the concrete SU(6) group type used by
the Weyl-matrix bridge.

The local abstraction in `GUT/SU6/ProtonStabilityNoGo/FlippedBranch/Flipped.lean` also checks:

- `TraceRepresentation.character_conjugation_fixed`
- `TraceRepresentation.fixedByConjugationMap`

The successful command was:

```text
lake build
```

with output:

```text
✔ [2312/2314] Built GUT.MathlibBridge
✔ [2313/2314] Built SU6NoGo
Build completed successfully (2314 jobs).
```

### Consequence

The conjugacy-invariance portion of the bridge is no longer merely informal.
The remaining assumptions are the connection to the relevant Weyl action and
the faithful passage from finite-dimensional SU(6) virtual characters to the
Laurent-polynomial restriction model.

---
