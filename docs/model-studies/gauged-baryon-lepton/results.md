# B/L Model: Residual Obstruction

## Result And Dictionary

The common-copy inlet is inapplicable to the charged species in the specified
N=1 dictionary with its actual residual baryon action. This is an action
obstruction, preceding any mass-map choice. A conditional Lean certificate also
forbids all four one-generation derivative-free dimension-six BNV families,
including physical qque. It does not certify all proton-decay channels.

Source inputs are [1304.0576v2](https://arxiv.org/abs/1304.0576v2), Sections II–IV,
Table I, Eqs.(11),(12): physical SM B,L charges, exotic charges ±3/2, and singlet
VEVs S_BL=(-3,-3), S_L=(0,-2). Both VEVs are assumed nonzero. The electroweak
Higgs is B,L-neutral. Work before its VEV. Use the product covering group; its
global quotient is not reconstructed here.

Normalize b=6B, l=2L to include the exotic charges integrally. All-left and
physical-right conventions are:

| Species | 6Y, all-left | (b,l), all-left | Physical carrier used in qque |
| --- | --- | --- | --- |
| Q | 1 | (2,0) | Q: (2,0) |
| uc | -4 | (-2,0) | uR, dual: (2,0) |
| ec | 6 | (0,-2) | eR, dual: (0,2) |
| dc | 2 | (-2,0) | dR, dual: (2,0) |
| L | -3 | (0,2) | L: (0,2) |

## Exact Residual Calculation

Torus angles x,y modulo 1 fix the VEVs iff 18x+6y and 4y are integers.
Consequently y=j/4 and x=k/36 with k+3j even: 72 elements of the product-cover
stabilizer. The charge matrix has Smith invariants 2,36. These values describe
this cover, not a claim about the faithful physical quotient.

In particular h=(1/18,0) survives, with order18. On physical (Q,uR,dR,L,eR)
it has cyclic charges (2,2,2,0,0). All four BNV family charges are 6 mod18;
qque has phase exp(2πi/3), hence is not invariant. Any full-stabilizer-invariant
coefficient would also be h-invariant, so this single witness suffices. Any
integer dressing by the two VEVs changes b by a multiple18 and cannot cancel6.
Changing to a faithful quotient cannot remove a transformation that acts
nontrivially on these fields; a formal descent identification remains unproved.

[ModelControls](../../../GUT/Common/ProtonProtection/ModelControls.lean),
`baryon_selection`, proves vanishing for the supplied one-generation cyclic
four-family dictionary using the existing SM/Lorentz/exterior completeness
interface. `baryon_qque_all_flavors` additionally proves physical qque vanishing for
arbitrary finite Q/u/e flavor index sets with these uniform charges. The
three-generation charge enumeration remains a supplementary exact check.

## Why Common S,T Fail

At h the entire Q copy space has scalar eigenvalue exp(2πi/9), whereas the
entire uc copy space has exp(-2πi/9). The N=1 exotics are colorless and supply
no extra Q or uc species. Injective embeddings of the same nonzero S into
these two full copy spaces would force its h-action to equal both distinct
scalars. `equal_scalars_of_common_embeddings` proves this necessary-condition
argument even when S was not assumed scalar. Hence no positive-dimensional
common source exists for this dictionary; changing T or mass parameters cannot
repair it. This is stronger than one failed attempted realization.

The selected charged SM species have no high-scale partners with matching
residual action in this dictionary. Charged exotics can have the same SM gauge
labels as ec/L; they carry different residual characters. Exotic
vector-like blocks and the neutral symmetric Majorana block may be massive or
tuned singular. The invariant-character prohibition does not require their
invertibility and remains valid on every subspace of these SM species. The
script includes massive and singular neutral controls, without claiming a
complete exotic mass classification or a post-EW massless spectrum.

## Stop And Evidence

The residual-charge endpoint and common-source obstruction are closed, conditional
on the supplied dictionary. Stop before full UV group/quotient, anomaly, exotic
mass classification, or all-operator stability certification.

See [exact checks](../../../tools/proton-protection-model-checks/README.md),
[strict audit](../../../GUT/Common/ProtonProtection/Audit/AuditModelControls.lean),
and [topic verification](../../topics/proton-protection-model-checks/verification.md).
The [journal paper](https://doi.org/10.1103/PhysRevLett.110.231801) remains the
source of the physical model, not a Lean theorem premise claiming its conclusions.

## Species-Dependent Theorem Recheck

See the [independent-species recheck](species-surplus-check.md) for the new Hom
surplus criterion, original-mass compatibility and remaining UV inputs.
