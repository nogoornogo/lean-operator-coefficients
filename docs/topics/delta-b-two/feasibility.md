# Six-Quark Basis Correspondence And Feasibility

## Historical checkpoint and current endpoint

The sections below preserve the original existence-pilot feasibility decision.
Statements such as "not yet formalized" and "no inverse is ready" describe that
checkpoint, not the current repository. The subsequently approved work proved:

- [Intrinsic completeness](../delta-b-two-completeness/README.md): dimension two
  and a two-probe inverse for the one-generation, derivative-free all-right
  degree `(2,4)` sector.
- [Conventional basis and normalization](../delta-b-two-conventional-basis/README.md):
  invertible Oi/Qi basis changes, an explicit charge-conjugation convention,
  and the Grassmann/species-factorial normalization bridge.
- [Multiplicity and actual-field interface](../delta-b-two-model-interface/README.md):
  the physical exterior sector is linearly equivalent to the residual Hom
  constrained by simultaneous typed exchanges, with both inverse identities
  and actual-field transport under supplied equivariant identifications.

All-chirality/full six-quark-basis generalization is deferred. General
multiplicities are not asserted to have dimension two. Physical matching,
RGE, matrix elements and oscillation rates remain outside these results.

## Literature correspondence

Rinaldi et al. organize the color-singlet, electrically neutral `uudddd`
operators into three conventional contraction families
`O^1`, `O^2`, and `O^3`. Their equations (1)--(3) define

- `O^3` by the diquark pattern `(u d)(u d)(d d)`, and
- its `AAS` color tensor by
  `epsilon_ijm epsilon_kln + epsilon_ijn epsilon_klm`.

The ordered map `DeltaBTwoSixQuark.orderedContraction` uses precisely this
species pairing, three right-Weyl epsilon contractions, and the same two-term
`AAS` color formula. It is therefore the two-component-Weyl realization of the
conventional `O^3_RRR` tensor pattern. The paper's chiral basis further states
`Q_1 = -4 O^3_RRR`. See [the conventional and chiral bases](https://arxiv.org/html/1901.07519#S2.SS1).

This is a tensor-pattern correspondence, not an assertion that the Lean
exterior coefficient has the paper's displayed normalization. Lean uses an
unnormalized six-slot alternatization; the explicit probe evaluates to `24`.
No four-component charge-conjugation convention or Grassmann-monomial
normalization bridge has been formalized. Those convention choices are
isolated from, and unnecessary for, the proved existence and nonzero result.

The same source states the four-dimensional Fierz relation
`O^2 - O^1 = 3 O^3`, reducing its overcomplete 18 conventional operators to 14
independent operators. In the all-right-handed electroweak-singlet sector,
`Q_1` and `Q_4` exhibit two independent structures: the proved `AAS/O^3`
direction and a second `SSS` direction. Consequently the present one-vector
existence theorem is not a coefficient-completeness theorem for that sector.

## What the pilot establishes

- The physical monomial has species degree `(2 upRight, 4 downRight)`,
  canonical dimension nine, `6Y = 0`, `3B = 6`, and lepton number zero.
- An ordinary Abelian residual character prohibits it exactly when the summed
  charge `-(2 up + 4 down)` is nonzero.
- The explicit `AAS` color and three-Weyl-epsilon contraction is invariant
  under the Standard Model gauge cover and the right-handed Weyl group.
- Its exterior descent is nonzero. A concrete one-generation basis probe gives
  the kernel-checked identity `witness_evaluation = 24`.
- The six-slot construction and all endpoint declarations pass strict
  transitive axiom audits with only `propext`, `Classical.choice`, and
  `Quot.sound` permitted.

These claims concern a local coefficient. They do not imply UV generation,
an oscillation amplitude, a neutron matrix element, or an oscillation time.

## Contraction-relation feasibility

Verdict: **manageable for a single frozen sector**.

The pilot shows that Lean can express the color and Lorentz contractions and
can reduce the fermionic alternatization to finite permutation support without
an unchecked oracle. For a basis theorem, however, contraction relations must
be structural rather than a growing list of coordinate evaluations. The
needed bounded interfaces are:

1. a degree-`(2,4)` restriction/projection theorem for the sixth exterior
   power, including its `2! 4!` normalization;
2. a classification of three right-Weyl pairings modulo the two-dimensional
   Schouten/Fierz relation;
3. a classification of the relevant six-fundamental color singlets, with the
   `AAS` and `SSS` representatives and their permutation symmetries; and
4. a proved translation of the combined color/spin relation to
   `O^2 - O^1 = 3 O^3` in the repository's conventions.

All four are finite exact algebra problems compatible with the pinned Lean
foundations. The nonzero proof also exposed an engineering warning: direct
expansion of all `6!` terms is too expensive. Future work should reindex by
species-preserving permutations and prove the factorial normalization once.

## Completeness feasibility decision

Verdict: **yes, conditionally and only for a separately approved bounded
sector; no direct qque-style inverse is ready today**.

A realistic next theorem would freeze the one-generation, derivative-free,
all-right-handed, Standard-Model-gauge-invariant degree-`(2,4)` sector and
prove that it is two-dimensional, with an `AAS/O^3` vector and one independent
`SSS` vector. An inverse map can then be defined by two probes after the four
interfaces above are proved. This is analogous in shape to the qque
coefficient theorem, but it is materially harder because both the color and
spin contraction spaces have nontrivial relations.

It is not realistic to begin with the complete 14-operator
`SU(3)_C x U(1)_EM` basis, all chirality sectors, evanescent operators, or
renormalized-scheme relations. Those enlarge the physical and mathematical
scope and cross into renormalization questions excluded by this project.

Stage 4 therefore has a positive feasibility result for the two-dimensional
all-right-handed sector, subject to a new user approval and a new frozen card.
No coefficient-completeness implementation has been started.

## Excluded calculations

The cited papers also discuss perturbative running, operator mixing, lattice
renormalization, and neutron matrix elements. They are literature context only.
This project does not formalize or numerically reproduce RGE evolution,
nonperturbative QCD/hadronic matrix elements, lattice or Monte Carlo work,
oscillation rates, or phenomenological bounds.

## Sources

- Rinaldi et al., [Lattice QCD determination of neutron-antineutron matrix elements with physical quark masses](https://arxiv.org/html/1901.07519), especially Sec. II.1, Eqs. (1)--(9).
- Buchoff and Wagman, [Perturbative Renormalization of Neutron-Antineutron Operators](https://arxiv.org/abs/1506.00647), for the renormalized-basis and evanescent-operator boundary that is excluded here.
