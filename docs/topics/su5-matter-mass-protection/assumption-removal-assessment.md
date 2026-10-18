# Removing Common Characters And The Dirac Ansatz

## Status And Scope

Feasibility assessment requested after checkpoint `checkpoint 01`, on the existing
`proof/su5-matter-mass-protection` branch. This document proposes next theorem
signatures; it adds no Lean theorem or new proof baseline. Master integration
is not authorized. Keep the actual standard SU(5) branching and pre-electroweak
SM-cover invariance; changing either changes the following argument.

## Arbitrary Symmetric Invariant Mass On The Current Carrier

Retain p tens, q dual tens and one bar-five, but start with an arbitrary
SM x H invariant symmetric complex-bilinear form B, rather than `ofDirac M`.
The actual branching has integral hypercharges 6Y:

| Branch | Q | up-left | electron-left | down-left | L |
| --- | --- | --- | --- | --- | --- |
| Source | 1 | -4 | 6 | 2 | -3 |
| Dual-ten target | -1 | 4 | -6 | absent | absent |

Only each ten species and its dual have opposite hypercharges. Invariance
therefore eliminates every other bilinear block, including all bar-five
blocks. For each remaining pair, irreducibility and the invariant evaluation
pairing should identify its SM-invariant bilinear maps with complex copy
matrices. Symmetry determines the reverse block. This would derive the species
Dirac form as a normal-form theorem, rather than assuming its construction.

This is a proposed classification for this carrier, not a completed Lean
result. Obligations: actual charge action, forbidden-block vanishing, actual
SM irreducibility/one-dimensional pairing spaces, extraction of the three
matrices, and equality of B with the reconstructed symmetric evaluation form.
Use those equalities to transport the already proved radical and exterior
result. Merely supplying a Dirac presentation certificate would not remove
this assumption. Electroweak breaking, new matter irreps and scalar-dependent
mass generation are outside this signature.

## General Residual Actions: Two Different Targets

Allow genuine H representations S and T on source and target copy spaces,
without requiring scalar action. If the same S/T occur for all ten species,
then H-invariant species mass matrices are intertwiners S → T. For finite H,
or finite-dimensional continuous compact H with the required semisimplicity,
write source/target constituent multiplicities as s_lambda/t_lambda. Every
species kernel has lambda multiplicity at least max(0,s_lambda-t_lambda).
Thus dim S > dim T ensures some common excess constituent in all three kernels.

A shared constituent W can give a nonzero map
`Sym² W → W ⊗ W`; injections of W into all three kernels and an equivariant
splitting on the Q side should produce the required coefficient map. The
actual-field/full-light exterior transport must also be proved. This is a
candidate extension preserving the common copy-representation origin, not a
claim that the general theorem is already formalized. A gauge-compensated
residual action additionally needs its species action dictionary and cancellation
bridge; it cannot be treated as untwisted common S merely by notation.

If instead source species actions are independent, copy-count excess alone
cannot guarantee qque. An algebraic SM-compatible illustration is zero mass,
p=1, q=0, H=C3, Q character 1, up-left a nontrivial character eta, and
electron-left character 1. Then `Hom_H(Sym² Q, up-left ⊗ electron-left)=0`.
This illustration does not assert full-SU(5) covariance, the earlier scalar/block
compensation mechanism, or an interacting proton-protecting model. It explains
why independently arbitrary species actions require an additional criterion.
It is a mathematical diagnostic, not a new Lean counterexample certificate.

## General Criterion Already Available

[QqueCommonIrreducible](../../../Physics/StandardModel/Operators/QqueCommonIrreducible.lean)
provides `coefficient_iff` under source symmetric-square semisimplicity. The
physical coefficient sector is nonzero precisely when the actual light
multiplicity representations `Sym² Q` and `up-left ⊗ electron-left` share a
simple constituent. Pairwise overlap of Q/up/electron is not the criterion.

Its `radical_nonzero_iff` / `radical_forbidden_iff` adapter accepts arbitrary
symmetric invariant mass and an actual compatible light SM action, with compact
H, continuity and the specified finite-dimensional/normed interfaces. These
existing conditional results already dispense with scalar characters and an
explicit Dirac formula at the criterion level. They do not derive the supplied
UV/light compatibility, identify this SU(5) carrier's kernels or guarantee
nonvanishing without checking its light multiplicities.

## Recommended Order And Stop Gates

1. Derive the arbitrary-invariant-mass normal form on the current carrier,
   retaining common chi. Endpoint: every such B satisfies the existing nonzero
   physical participating-field theorem when p > q. Stop if a forbidden block
   survives or the actual SM pairing-space bridge cannot be supplied.
2. Replace common chi by common genuine finite-H copy representations S/T.
   Endpoint: derive light constituent embeddings from arbitrary equivariant
   matrices and prove physical qque nonzero when dim S > dim T. Require an
   actual exterior transport/splitting certificate; a virtual index alone is
   insufficient. Keep independent species actions outside this theorem.
3. For independently varying species actions, apply the general completeness
   criterion to actual mass kernels and classify permitted/forbidden qque.
   No universal nonzero conclusion or all-BNV protection claim is proposed.

These steps remove presentation assumptions while retaining explicit model
structure. No new scalar dynamics, UV Yukawa origin, matching or rates are
required for the proposed exact algebraic endpoints.
