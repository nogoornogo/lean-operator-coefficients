# Literature and use boundaries

Consulted stage 01. These are proof-design references, not imported axioms
or completeness hypotheses. The fixed LLHH theorem reuses local checked
proofs; it does not certify these papers in full.

1. Martin Rubey and Bruce W. Westbury, *Combinatorics of symplectic invariant
   tensors*, [arXiv:1504.02586v1](https://arxiv.org/pdf/1504.02586v1), section 2:
   Theorem 2.2 (contraction generation), Theorem 2.13 (relations), Theorem
   2.18 (noncrossing diagram basis). For a two-dimensional complex defining
   representation, this gives the epsilon-contraction route. Their odd-vector
   diagram convention carries signs: do not copy diagram permutations without
   translating to our exterior statistics. SU(2)/SL(2) transport remains a
   mathematical obligation wherever needed, not a consequence of citation.
2. J. S. Milne, *Algebraic Groups*,
   [author's 2022 text](https://www.jmilne.org/math/Books/iAG2022.pdf), section
   4.i, Proposition 4.33 and Corollary 4.34: invariants are the kernel of the
   coaction minus the trivial coaction, and invariants commute with extension
   of the base field. This suggests exact coefficient comparison and rational
   models. It does not supply our model/complexification bridge. General
   coaction formalization is not needed for this fixed LLHH route.
3. Landon Lehman and Adam Martin, *Hilbert Series for Constructing Lagrangians:
   expanding the phenomenologist's toolbox*,
   [arXiv:1503.07537](https://arxiv.org/abs/1503.07537), Phys. Rev. D 91,
   105014 (2015): symmetry/statistics-aware invariant counting, especially
   without derivatives. A future compression guide, not a constructed basis
   or a proof of equality with our kernel.
4. Juan Carlos Criado, *BasisGen: automatic generation of operator bases*,
   [arXiv:1901.03501](https://arxiv.org/abs/1901.03501) (2019): roots and
   weights for representation generation and decomposition. Future exact
   counting implementation guidance; no software output is a Lean premise.

The already checked `WeinbergResidualHom`, `WeinbergSMInterface`, and
`LiWeinbergCertificate` implement the fixed-sector contraction, reconstruction
and symmetric flavor coordinates. The new obligation is their connection to
the generic statistical content carrier and its constraint rank. Finite
complex coordinates do not make arbitrary complex numbers executable; the
rank certificate uses structural dimension proofs, not numerical elimination.
