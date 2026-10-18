# THEORY

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

# Theory summary for independent reconstruction

This document preserves the **historical reconstruction sketch**, not the
current theorem statement or work queue. Its tentative claims and unresolved
language record that stage of the investigation and are not proof certificates.
For the checked model classes, including nonlinear scalar sources and positive
family-dependent charge profiles, use [ASSUMPTIONS.md](../../../proof/ASSUMPTIONS.md),
[PROOF_STATUS.md](../../../proof/README.md), and their linked dossiers. In particular,
do not infer a nonzero decay amplitude from this sketch.

---

# 1. Starting problem

The original question was whether a 4D simple SU(6) grand-unified theory could give **exact proton stability** naturally, while keeping the low-energy chiral matter equal to the Standard Model (plus possible gauge singlets).

Early model-building attempts used split multiplets to separate Q, u^c, e^c, d^c, and L into different SU(6) multiplets. Increasingly elaborate matter contents could suppress some gauge-mediated proton-decay overlaps, but exact all-order protection repeatedly required either tuned numerical relations or residual symmetries that were incompatible with the chiral spectrum.

This motivated a shift from constructive model building to a no-go strategy.

---

# 2. Standard SU(6) subgroup structure

A preferred block embedding is

\[
6=(3,1)+(1,2)+(1,1).
\]

The centralizer of SU(3) × SU(2) in SU(6) is rank 2. A convenient basis is a standard SU(5)-like hypercharge generator \(Y_5\) and an orthogonal generator \(X\).

A general hypercharge embedding can be written symbolically as

\[
Y=aY_5+bX.
\]

The investigation found strong evidence, and a proposed symbolic proof, that exact SM-only chiral matter permits only two physically relevant branches:

## Standard branch

\[
6Y=(-2,-2,-2,3,3,0).
\]

This is the usual SU(5)-chain hypercharge.

## Flipped branch

\[
6Y=(1,1,1,0,0,-3).
\]

This corresponds to the familiar flipped rearrangement at the SU(5) level.

The proof of this dichotomy is not yet independently verified and should eventually be formalized or replaced by a cleaner theorem.

---

# 3. Standard branch obstruction

For the standard SU(5) chain, the key proposed theorem is a charge-resolved Weyl-orbit statement.

At fixed residual Abelian charge t, SM-only chiral matter must be the restriction of a virtual SU(5) representation. Because Q, u^c, e^c lie in the same SU(5) 10 Weyl orbit and d^c, L lie in the same \bar5 orbit, the net chiral index at fixed charge has the form

\[
I_t=n_{10,t}(Q+u^c+e^c)+n_{\bar5,t}(d^c+L)+s_t1.
\]

Thus

\[
n_Q(t)=n_u(t)=n_e(t),
\qquad
n_d(t)=n_L(t).
\]

For an ordinary residual Abelian symmetry with charges \(k_f\), the two usual dimension-6 proton-decay charge combinations are

\[
P_1=2k_Q-k_u-k_e,
\]

\[
P_2=k_Q+k_L-k_u-k_d.
\]

The orbit equalities force both to vanish on the relevant charge sectors, so the residual symmetry cannot forbid those gauge-mediated ΔB=1 operators.

A logically separate continuous-U(1) cross-check rewrites the same proton functionals in terms of mixed anomalies:

\[
P_2=A_2-A_3,
\]

\[
P_1=\frac13A_3+\frac12A_2-A_{YYK}.
\]

If the protecting U(1) is exact and anomaly-free, both vanish automatically.
This anomaly factorization does not prove the finite Abelian case and is not
the main standard-branch argument.  The intended standard proof is the
charge-resolved Weyl-orbit statement followed directly by the Abelian
charge-group calculation; it must include finite residual charge groups.

This branch is believed to be closed under the stated assumptions, but the final theorem statement should be rewritten cleanly and separately verified.

---

# 4. Flipped branch: proposed stronger obstruction

The most promising remaining escape route was the flipped hypercharge embedding

\[
6Y=\mathrm{diag}(1,1,1,0,0,-3).
\]

The proposed result is stronger than a proton-decay statement: it says the SM chiral spectrum itself cannot arise as the restriction of any finite virtual SU(6) representation.

## 4.1 Flipped maximal-torus parameterization

Use SU(6) torus coordinates \(z_1,\ldots,z_6\) with

\[
\prod_{i=1}^{6} z_i=1.
\]

The flipped SM torus is parameterized as

\[
(z_1,z_2,z_3,z_4,z_5,z_6)
=(a_1t,a_2t,a_3t,b,b^{-1},t^{-3}),
\]

with

\[
a_1a_2a_3=1.
\]

Equivalently, inside the SU(6) torus it satisfies

\[
z_4z_5=1
\]

and hence also

\[
z_1z_2z_3z_6=1.
\]

The proposed normalizer statement is that permutations of indices \(\{1,2,3,6\}\) preserve this subtorus. Therefore restricted SU(6) characters must be invariant under an S4 action extending the manifest color S3.

This normalizer statement is critical and must be proved carefully.

---

## 4.2 Fundamental chiral character

Let

\[
C=\chi_{3},\qquad \bar C=\chi_{\bar3},\qquad W=\chi_2.
\]

For the flipped embedding,

\[
6=(3,1)_1+(1,2)_0+(1,1)_{-3},
\]

so

\[
D_6:=\chi_6-\chi_{\bar6}
=Ct-\bar Ct^{-1}+t^{-3}-t^3.
\]

In torus coordinates this can be written as

\[
D_6=\sum_{i\in\{1,2,3,6\}}(z_i-z_i^{-1}),
\]

which is manifestly symmetric under permutations of \(\{1,2,3,6\}\).

---

## 4.3 One-generation SM chiral character

Use integer hypercharge \(6Y\):

\[
Q:1,\qquad u^c:-4,\qquad d^c:2,\qquad L:-3,\qquad e^c:6.
\]

The particle-minus-antiparticle character is

\[
\begin{aligned}
F_{SM}={}&CWt-\bar CWt^{-1}\\
&+\bar C(t^{-4}+t^2)-C(t^4+t^{-2})\\
&+W(t^{-3}-t^3)\\
&+(t^6-t^{-6}).
\end{aligned}
\]

The proposed exact factorization is

\[
\boxed{
F_{SM}=D_6\left(W-t^3-t^{-3}\right)
}
\]

and should be verified algebraically in Lean.

Define

\[
A:=W-t^3-t^{-3}.
\]

On the flipped torus,

\[
W=z_4+z_5,
\qquad
z_6=t^{-3},
\qquad
z_6^{-1}=t^3,
\]

so

\[
A=z_4+z_5-z_6-z_6^{-1}.
\]

Under the permutation \((3\;6)\),

\[
A\mapsto z_4+z_5-z_3-z_3^{-1},
\]

which is not equal to A generically.

If every restricted SU(6) virtual character must be invariant under this permutation, then F_SM cannot be such a restriction because D_6 is invariant but A is not. Since the coordinate ring is an integral domain and D_6 is nonzero, cancellation gives a contradiction.

This is the central proposed flipped-branch proof.

---

# 5. Why the flipped result matters

If the flipped branch is truly impossible at the level of the SU(6) representation ring, then no SU(6)^3 anomaly argument is needed for that branch.

The logic of the intended final theorem becomes:

1. only one semisimple SU(3) × SU(2) embedding is viable;
2. SM-only hypercharge embeddings reduce to standard or flipped;
3. flipped cannot realize the SM chiral spectrum at all;
4. standard can realize the spectrum, but no ordinary residual Abelian internal symmetry can forbid the relevant ΔB=1 gauge operators;
5. therefore no ordinary Abelian charge selection rule can enforce exact
   Delta-B = 1 prohibition under the assumptions.

Step 4 is a selection-rule statement: it requires construction of the relevant
gauge- and Lorentz-invariant local operator classes and proof that the residual
Abelian symmetry leaves one of them neutral.  It does not by itself assert a
nonzero Wilson coefficient or an unavoidable proton-decay amplitude.  Such a
dynamical statement is a separate, stronger corollary requiring an explicit
channel-presence premise.

The Lean operator-class bridge uses the physical-field signatures
`q_L q_L u_R e_R` and `d_R u_R q_L l_L`.  It checks hypercharge neutrality,
canonical dimension six, `Delta B = Delta L = 1`, and explicit color, weak,
and chiral-spinor epsilon contraction plans.  Determinant invariance and
nonvanishing of the epsilon tensors are proved separately, and the two
residual characters are identified with `P_1` and `P_2`.  Conversely, the
integer quantum-number constraints classify every four-slot signature as one
of these two field-multiplicity patterns up to slot order, so the two character
tests exhaust this declared operator model.  This is the precise EFT
operator-class meaning of "physically admissible" used by the formal
selection-rule theorem; it intentionally says nothing about a generated
coefficient or matrix element.

---

# 6. What must be checked before accepting the theorem

The most important possible failure modes are:

1. The claimed S4 normalizer of the flipped SM torus may be too large or may not act in the required way on the embedded subgroup.
2. The restriction of an SU(6) character may be invariant only under a smaller quotient action than assumed.
3. The torus coordinate ring may have relations that make the apparent non-invariance vanish after quotienting.
4. The factorization of F_SM may be correct algebraically but not represent the actual chiral character of the embedded subgroup.
5. The standard/flipped hypercharge classification may have missed an additional branch.
6. The standard-branch residual-symmetry argument may need stronger hypotheses on family dependence / Yukawa mixing than currently stated.

A correct formalization should make these issues explicit instead of hiding them in informal notation.
