# source-provider-free D2/D3 function-level no-uplift theorem

Environment-specific paths were normalized at stage 02; recorded outcomes are unchanged. Commands assume elan, lake and lean on PATH and execution from the repository root.

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex + qwen3.6-35b-a3b / Lean 4.33.1

- Reviewer/tool: Codex orchestrating local `qwen3.6-35b-a3b` reasoning and
  Lean/Lake kernel checks
- Version: Lean 4.33.1, Lake 5.0.0, mathlib v4.33.1
- Scope: source-provider-free D2/D3 function-level no-uplift theorem

### Claim checked

Every finite virtual representation of the concrete `SU(6)` group has a
restricted trace character fixed by the `(3 6)` Weyl representative.  Hence it
cannot equal the canonical flipped-SM Laurent target, whose evaluator is
faithful and whose normalized polynomial is not `swap36`-fixed.  The same
obstruction applies to every nonzero generation number and remains after adding
an arbitrary virtual multiplicity of gauge singlets.

### Result

- [x] confirmed
- [ ] counterexample found
- [x] proof gap found
- [x] assumption missing
- [ ] inconclusive

### Details

The local-model audit confirmed that source-side Laurent polynomiality and a
global torus eigenbasis theorem are unnecessary for this implication: trace
conjugacy invariance supplies source fixedness directly.  A preliminary
suggestion that target-torus character injectivity was required was rejected
after checking the direction of the desired contradiction; only the forward
character map is needed.

Lean kernel-checks now include:

- `legacyFlippedSMCharacter_eq_flippedSMCharacter`
- `legacyFlippedSMCharacterExplicit_eq_flippedSMCharacterExplicit`
- `no_restrictedCharacter_eq_diagonalLaurentEval_of_not_swap36_fixed`
- `no_restrictedCharacter_eq_flippedSMCharacter_eval`
- `flippedSMCharacterEval_not_mem_finiteVirtualRestrictedCharacterImage`
- `no_restrictedCharacter_eq_nonzero_generation_flippedSMCharacter_eval`
- `no_restrictedCharacter_eq_nonzero_generation_add_singlets_eval`
- `PhysicalRestrictionBridge.restrictVirtual_character_on_torus`
- `PhysicalRestrictionBridge.flippedSMTarget_character_not_mem_restrictionImage`
- `AuditD2D3.audit7_physical_group_character_image_bridge`
- the corresponding public checks in `GUT/SU6/ProtonStabilityNoGo/Audit/AuditD2D3.lean`

The finite permutation-coordinate checks formerly using `native_decide` were
replaced by ordinary kernel-reduced `decide` proofs.  `#print axioms` for the
four public audit theorems reports only `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorryAx` or native-code decision axiom.

The successful command was:

```text
lake build
```

with output:

```text
✔ [3672/3672] Built GUT.AuditD2D3 (3.0s)
✔ [3673/3674] Built SU6NoGo (2.0s)
Build completed successfully (3674 jobs).
```

### Consequence

Critical audit points 3 and 7 no longer depend on constructing
`SU6TorusEigenbasisTheory` for every source representation.  To obtain the
literal representation-ring statement in `R(G_SM)`, the remaining bridge is to
instantiate the physical flipped-SM group, homomorphism and torus lift, construct
the target virtual representation, and prove that its restricted torus character
is the checked canonical target.  A quotient-level representation-ring package
is still needed if the conclusion is to use literal `R(G_SM)` notation.  A full
relative `S4` formalization remains optional for the present contradiction.

---
