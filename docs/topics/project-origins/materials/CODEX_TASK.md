# CODEX_TASK

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

# Codex task: first formal-verification milestone

**Historical task specification.** This first milestone and later scoped
extensions have been completed. The instructions below are preserved as an
audit record, not the current work queue or a limit on the checked library.
Use [Topic records](../../README.md) for current work and
[ASSUMPTIONS.md](../../../proof/ASSUMPTIONS.md) for the present model boundaries.

## Mission

Do **not** assume the proposed no-go theorem is true.

Your first job is to independently reconstruct and either prove or refute the proposed **flipped-branch representation-ring obstruction**.

The immediate milestone is not the full SU(6) no-go theorem.

---

# Target statement (informal)

For flipped hypercharge

\[
6Y=\mathrm{diag}(1,1,1,0,0,-3),
\]

the Standard Model one-generation chiral character is not the restriction of any finite virtual SU(6) representation.

Symbolically:

\[
F_{SM}^{flip}
\notin
\mathrm{Im}\left(R(SU(6))\to R(G_{SM})\right).
\]

---

# Required adversarial checks before coding

1. Re-derive the flipped torus embedding from scratch.
2. Compute the normalizer of that torus/subgroup inside the SU(6) Weyl group.
3. Verify whether the claimed transposition (3 6) genuinely preserves the relevant embedded torus.
4. Verify the one-generation SM chiral character and all integer hypercharge exponents.
5. Verify the factorization
   \[
   F_{SM}=D_6(W-t^3-t^{-3}).
   \]
6. Search manually/algebraically for a counterexample virtual SU(6) character before attempting the no-go proof.
7. If any step fails, stop and record the counterexample or gap in `notes/review-log.md`.

---

# Lean strategy

Prefer a **minimal algebraic formalization** first.

Do not formalize compact Lie groups, Haar measure, or the full representation theory of SU(6) unless necessary.

Suggested layers:

## Layer 1 — Laurent polynomial / group algebra model

Represent the character ring of the torus by a Laurent polynomial or group-algebra object over an exponent lattice.

Needed facts:

- integral-domain property,
- action of finite permutations on exponent coordinates,
- explicit torus quotient relations / sublattice parameterization.

## Layer 2 — explicit flipped character algebra

Formalize:

- `D6`,
- `FSM`,
- `A`,
- the factorization `FSM = D6 * A`,
- `D6 ≠ 0`,
- the relevant permutation fixes `D6`,
- the same permutation does not fix `A`,
- hence it does not fix `FSM`.

## Layer 3 — representation-theoretic bridge

Prove or import the statement:

> Restriction of an SU(6) virtual character to the chosen torus is invariant under every Weyl element that normalizes/preserves that torus.

Be explicit about whether this is proved from conjugacy-invariance of trace, from `R(T)^W`, or from a direct permutation-matrix argument.

## Layer 4 — no-uplift theorem

Derive the contradiction:

```lean
 theorem no_flipped_sm_uplift :
   ¬ ∃ χ : SU6VirtualCharacter,
       restrictFlipped χ = flippedSMCharacter := by
   ...
```

The exact types may differ.

---

# Important implementation rule

Do not encode the desired conclusion as an assumption.

Examples of unacceptable shortcuts:

- defining `SU6VirtualCharacter` to mean "an invariant Laurent polynomial" without proving that this model faithfully contains all virtual SU(6) characters and that the relevant restriction map is represented correctly;
- assuming the relative-Weyl invariance theorem as an opaque axiom;
- quotienting by relations that already impose the desired non-uplift;
- proving only the explicit polynomial non-invariance and claiming that this alone proves the SU(6) theorem.

If an unformalized standard theorem must be used temporarily, isolate it behind one clearly named lemma and mark it `TODO/UNTRUSTED-BRIDGE`.

---

# Deliverables for milestone 1

1. `GUT/SU6/ProtonStabilityNoGo/FlippedBranch/Flipped.lean`
2. Any helper modules required.
3. `lakefile.toml` or `lakefile.lean`
4. `lean-toolchain`
5. `lake-manifest.json`
6. A successful `lake build` log.
7. `notes/review-log.md` updated with:
   - any failed proof attempts,
   - any gaps,
   - any counterexamples,
   - exact assumptions still outside Lean.
8. A short `FORMALIZATION_STATUS.md` separating:
   - kernel-checked theorem,
   - imported theorem,
   - unformalized physics assumptions.

---

# Do not proceed automatically to the full theorem

After milestone 1, stop and review the result.

Only if the flipped obstruction survives should the next stages be:

1. hypercharge standard/flipped classification,
2. standard-branch residual-symmetry obstruction,
3. semisimple embedding classification,
4. final no-go composition.
