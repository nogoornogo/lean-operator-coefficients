# exploration-history

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

# Exploration history

This is a compressed history of the investigation. It is context, not proof.

## 1. Initial goal

Explore whether 4D simple SU(6) can give exact proton stability naturally while reproducing only the Standard Model chiral spectrum at low energies.

The working preference was:

- simple gauge group,
- exact proton stability rather than merely a long lifetime,
- no extra light chiral exotics,
- avoid finely tuned numerical mass relations,
- increase matter/Higgs complexity only when simpler constructions fail.

---

## 2. Constructive split-multiplet attempts

Several anomaly-free matter contents were explored.

### F47

\[
15+2\bar6+20.
\]

Motivation: use the extra 20 to place Q, u^c, e^c in different SU(5)-like sources.

Result: specific 10-sector Clebsch relations generated an algebraic obstruction to the desired orthogonality; the \bar5 sector also failed without tuning.

### F67

\[
15+2\bar6+2(20).
\]

An adjoint 35 with missing-VEV alignment could protect one 10-sector direction group-theoretically, but the \bar5 sector still required numerical tuning.

### F79

\[
15+3\bar6+6+2(20).
\]

The \bar5 sector could be split more naturally using multiple adjoint alignments, but the 10 sector remained incomplete.

### F99

\[
15+3\bar6+6+3(20).
\]

Multiple 20s plus several adjoint VEV alignments allowed a tree-level pure split of Q, u^c, e^c, d^c, L.

However, exact all-order texture protection became the problem: multiple VEV-carrying fields with the same gauge quantum numbers could not be distinguished by a simple unbroken ordinary Abelian symmetry in the required way.

A 189_H direction and antisymmetric flavor couplings gave interesting partial improvements, but remaining relations were not symmetry-protected.

---

## 3. Pivot from construction to no-go

The repeated failure mode suggested that the problem might not be insufficient matter content but a deeper incompatibility between:

- simple SU(6),
- SM-only chiral matter,
- exact residual symmetry,
- proton stability.

The investigation therefore shifted to matter-independent arguments.

---

## 4. Standard-embedding residual-symmetry obstruction

For the standard SU(5) chain, SU(5) Weyl orbits tie together:

- Q, u^c, e^c inside a 10-type chiral index,
- d^c, L inside a \bar5-type chiral index.

This led to charge-resolved equalities that make the ordinary gauge-mediated proton-decay operators neutral under any compatible residual Abelian symmetry.

A continuous-U(1) version related the proton charge functionals directly to mixed anomalies.

---

## 5. Discrete-remnant exploration

A promising Z9/Z3 construction based on a generator proportional to

\[
\mathrm{diag}(1,1,1,0,0,-3)
\]

was examined.

A charge-shift theorem was derived for the standard chain, and combining it with realistic Yukawa / CKM requirements left only:

- a charge pattern that failed to protect the proton, or
- a family-charge pattern that killed realistic CKM mixing.

This closed the most promising standard-branch discrete escape route under the working assumptions.

---

## 6. Classification of SU(6) embeddings

The semisimple SU(3) × SU(2) embedding was reduced to the block decomposition

\[
6=(3,1)+(1,2)+(1,1).
\]

The centralizer is rank 2, so there is an infinite family of symbolic hypercharge slopes.

A finite exact branching search found many local SM-like slopes in high representations, but after imposing complete chiral-index constraints almost all disappeared.

This motivated a symbolic classification.

---

## 7. Standard / flipped hypercharge branches

A proposed representation-ring argument reduced the physically viable SM-only branches to:

### Standard

\[
6Y=(-2,-2,-2,3,3,0).
\]

### Flipped

\[
6Y=(1,1,1,0,0,-3).
\]

The standard branch was already constrained by the residual-symmetry no-go, leaving the flipped branch as the final possible embedding class.

---

## 8. Flipped branch obstruction

The current proposed key result is that the one-generation SM chiral character for flipped hypercharge is not invariant under an extra Weyl permutation that preserves the embedded torus, whereas every restricted SU(6) character must be invariant.

If correct, this is stronger than an anomaly argument: the flipped SM chiral character is not in the restriction image of the virtual SU(6) representation ring at all.

This is now the highest-priority formalization target.
