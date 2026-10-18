# Flipped-branch Laurent-polynomial algebra from CODEX_TASK.md

Environment-specific paths were normalized at stage 02; recorded outcomes are unchanged. Commands assume elan, lake and lean on PATH and execution from the repository root.

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Reviewer/tool: Codex with Lean/Lake
- Version: Lean 4.33.1, Lake 5.0.0
- Scope: Flipped-branch Laurent-polynomial algebra from `CODEX_TASK.md`

### Claim checked

The explicit flipped one-generation SM chiral character factors as

```text
F_SM = D6 * (W - t^3 - t^-3)
```

after rewriting on the flipped SU(6) subtorus with coordinates
`z1,z2,z3,z4`, `z5 = z4^-1`, and `z6 = (z1*z2*z3)^-1`.
The `(3 6)` Weyl transposition fixes `D6` but does not fix `A`, and the full
SM character is not fixed.

### Result

- [x] confirmed
- [ ] counterexample found
- [x] proof gap found
- [x] assumption missing
- [ ] inconclusive

### Details

Kernel-checked in `GUT/SU6/ProtonStabilityNoGo/FlippedBranch/Flipped.lean`:

- `weak_relation_z4_z5`
- `su6_torus_relation`
- `swap36_preserves_weak_relation`
- `swap36_preserves_su6_torus_relation`
- `flippedSM_factorization`
- `swap36_D6`
- `swap36_A_ne`
- `swap36_flippedSM_ne`
- `swap36_flippedSMExplicit_ne`
- `no_flipped_sm_uplift_conditional`

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

The proof intentionally models only the Laurent-polynomial character algebra.
The theorem `no_flipped_sm_uplift_conditional` assumes, rather than proves, the
representation-theoretic bridge: every finite virtual SU(6) character restricts
to a polynomial invariant under the modeled `(3 6)` action. The closed
polynomial equalities and inequalities are discharged with Lean's `decide`.

### Consequence

The explicit algebraic obstruction survived the first Lean check. The next
critical task is to formalize or independently prove the bridge from SU(6)
virtual characters to `swap36`-invariance on the flipped subtorus. The full
SU(6) no-go theorem remains unproved.

---
