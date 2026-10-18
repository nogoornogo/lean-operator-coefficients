# Source Recovery And Scope Decision

## Primary Route: Li Dimension-Nine Basis

[Li et al., arXiv:2007.07899v1](https://arxiv.org/pdf/2007.07899v1#page=46)
was downloaded and equation (5.63), PDF/printed page 46, inspected visually.
The first block is `O_(u²d⁴)^(1–10)`: ten Young-projected candidates, not two
unflavored operators or ten independent scalar coefficients.

All ten use the spin seed `(d_pa C d_td)(u_ue C d_rb)(u_vf C d_sc)`.
Paper species order by flavor labels is D_p,D_r,D_s,D_t,U_u,U_v.
The repository order is U,D,U,D,D,D. Color seeds shown are products of two
epsilons with index triples `ace/bdf`, `adf/bce`, `abe/cdf`, `abf/cde`.
These are data recovered from the paper. The implemented epsilon dictionary
is specified below; a four-component C-matrix normalization is not asserted.

The down/up shape pairs, in printed order, are:

| Candidates | Down shape | Up shape |
|---|---|---|
| 1,2 | (3,1) | (1,1) |
| 3,4 | (2,1,1) | (1,1) |
| 5,6 | (4) | (2) |
| 7 | (3,1) | (2) |
| 8,9 | (2,2) | (2) |
| 10 | (2,1,1) | (2) |

The tableaux, not just the shapes, are part of the candidate specification.
Equation (4.33), page 24, uses a normalized Young action; (4.34), page 25,
moves that action to coefficients by inverting every constituent permutation.
Thus a flavor coefficient implementation must distinguish operator action from
dual coefficient action. Simply attaching unrestricted residual tensors to
the four bare color seeds would not verify the printed ten-term basis.

## Second Route: Conventional Neutron Basis

[Rinaldi et al., arXiv:1901.07519v2, section II.1](https://arxiv.org/html/1901.07519#S2.SS1)
was inspected for the conventional O1/O2/O3 contractions, color SSS/AAS tensors
and chiral basis. That route matches the existing scalar-flavor conventional
[certificate](../delta-b-two-conventional-basis/README.md). It does not supply
the missing general-generation Young decomposition needed for this topic's
additional endpoint. No lattice, renormalization or matrix-element result is used.

## Existing Interfaces And Initial Certificate Gap

[YoungTensorProjector](../../../Math/RepresentationTheory/YoungTensorProjector.lean)
constructs a normalized projector for a supplied tableau, its stable image and
kernel quotient. It explicitly does not prove a full family decomposition.
[TwoSlotYoung](../../../Math/RepresentationTheory/TwoSlotYoung.lean) handles the
up pair. The [typed-flavor classification](../delta-b-two-model-interface/flavor-hom.md)
already gives the full physical sector as constrained 25 local coordinates.

At the source-recovery checkpoint, the missing task was a concrete certificate connecting Li's specified ten
projected seeds to that local permutation representation: action convention,
normalization, independence of repeated shape copies, spanning, and inverse
transport of arbitrary residual coefficient maps. Individual projector
idempotence alone proves none of the required cross-component claims.
The abstract isotypic results provide tools, not an identification of their
chosen copies with these ten particular published seeds.

This is a bounded instance of deferred
[roadmap 2](../derivative-free-completeness/README.md#remaining-roadmap), not
an impossibility result and not evidence that new general Young theory is needed.
Source recovery succeeded. The approved extension and current proof endpoint
are recorded in the [dossier](../../proof/current/applications/Physics/LI_SIX_QUARK_BASIS.md).

## Approved Bounded Milestone

The user approved a bounded additional milestone within this topic: construct the literal
ten-tableau dictionary and certify its S4×S2 local decomposition before the
general-flavor physical inverse. Retain the arbitrary residual group and distinct
carriers, and all physical non-goals. Do not expand to all tableaux, all sectors,
or general p/y/m algorithms. Its exploratory check reached the scope gate
described in [the rank investigation](rank-investigation.md); it did not
establish the requested two-sided Lean certificate.

## Implemented Epsilon Dictionary And Extension

The first ten color seeds, in zero-based order, are `ace/bdf`, `adf/bce`,
`ace/bdf`, `adf/bce`, `ace/bdf`, `abe/cdf`, `adf/bce`, `ace/bdf`,
`abf/cde`, `ace/bdf`. The spin pairs are `(0,3),(4,1),(5,2)` in paper order.
The paper-to-repository slot map is `[1,3,4,5,0,2]`.

`LiSixQuarkConvention` defines signed row-column Young sums using the visually
checked tableaux and all 48 within-species permutations. Moving permutations
onto local contractions includes the fermion sign. Each candidate is divided
by the nonzero primitive-coordinate divisor
`[2,2,1,2,2,2,2,2,2,1,2]`, including the extra seed last. This fixes the
certificate's convention; it does not assert equality with the paper's
hook-length-normalized projector or a four-component C-matrix scale.
`candidate_coordinates` checks the literal epsilon contractions against
independent repository coordinates. Source transcription remains the explicit
dictionary, not an assumed external completeness theorem.

The added eleventh seed uses `ace/bdf`, the same spin pairs, and the local
character trivial on down permutations and alternating on the up pair. After
the fermion transfer it is alternating down / symmetric up flavor. It is not
presented as part of the printed ten-term list. The selected 25 orbit vectors
and their typed residual-Hom transport replace the abandoned ten-only endpoint;
a complete eleven-factor Schur decomposition is not claimed.
