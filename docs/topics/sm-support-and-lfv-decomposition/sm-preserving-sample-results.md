# SM-Preserving Samples: Common Factors and Tensor Support

## Endpoint

The two [contract](sm-preserving-sample-contract.md) routes are complete.
An actual inner color action passes the standard SM normalization gate but is
invisible to gauge-invariant coefficients. Two independent S3 flavor actions
also preserve SM gauge action, yet have opposite actual qque support. Neither
is a protecting SU(6) model or a certificate of full B1 prohibition.

| Input | SM gate | Actual qque result | Further input gate |
| --- | --- | --- | --- |
| The embedded signed color probe acts by conjugation | A cover compensator is explicitly constructed | Its gauge factor cannot change an invariant coefficient | No new mass/VEV candidate is constructed |
| Q=three-dimensional permutation, u=three trivial copies, e=three sign copies of S3 | Independent flavor commutes with actual SM gauge action | Every actual qque coefficient is zero | No common Q/u multiplicity dictionary; no injective Q-to-u invariant map |
| Q=three-dimensional permutation, u=e=three sign copies of S3 | Same SM commutation certificate | An actual nonzero qque coefficient exists | No shared Q/sign constituent; every Q-to-u invariant map is zero |

The flavor conventions here are physical right-handed u/e, as in the actual
ordered/exterior coefficient dictionary. The corresponding left-handed
uc/ec representations are dual. Gauge preservation is not full SM
phenomenological compatibility, anomaly freedom or a SU(6) lift.

## Actual coefficient proofs

[S3QqueTensorSamples](../../../Physics/StandardModel/Operators/S3QqueTensorSamples.lean)
constructs all three-dimensional actions. Q acts by genuine permutations,
the sign representation acts by the sign character on each of three copies,
and the trivial action fixes all three copy coordinates.

For (Q,trivial,sign), `entry_swap` derives a minus sign from any transposition
on a residual coefficient. The existing physical qque dictionary requires
symmetry of the Q flavor pair. For a diagonal pair, an odd transposition
fixing its index forces zero; for a distinct pair, swapping the two indices
and symmetry also forces zero. All basis entries vanish, hence the whole
residual space vanishes. `forbidden_permutation_trivial_sign` transports this
through the actual physical exterior coefficient equivalence. It does not
assume a raw invariant tensor descends nontrivially.

For (Q,sign,sign), `positiveCoefficient` is the invariant product

    (sum x)(sum y)(sum z)(sum r).

The two sign characters cancel, and the Q sums are permutation-invariant.
The coefficient is symmetric in Q, evaluates to one on a named basis tensor,
and reconstructs a nonzero actual physical exterior coefficient via
`allowed_permutation_sign_sign`.

`no_q_to_sign` and `no_shared_q_sign` prove absence of a shared irreducible
between Q and the sign-copy representation. The latter derives semisimplicity
from the actual finite S3 action over C, with group order six; no user-supplied
decomposition or extra semisimplicity assumption is added. Thus failure of
the common-single-factor witness is not evidence of qque prohibition:
the positive sample still has tensor support after two sign factors cancel.

`independent_flavor_preserves_sm` proves commutation of the actual independent
SM and flavor factors for the fields; preservation is not inferred from a
numerical charge table.

## The inner color sample

[SMNormalizingColorSample](../../../GUT/SU6/SelectionRules/Models/SMNormalizingColorSample.lean)
reuses the actual embedded color probe but changes the test: the generator
itself is now inside the SM image. `beta` is conjugation by its actual cover
representative, and `normalizes` proves the required cover relation.
`invariant_color_factor` proves that every actual gauge-invariant functional
is unchanged by this factor. This is a concrete instance of existing gauge
removal, not a new exclusion of all normalizers or a full residual model.

## Realization and neutral-Higgs flavor-map gates

`no_uniform_flavor_dictionary` shows the Q/u species in both unequal samples
cannot simultaneously be identified with a single flavor representation.
Consequently the previous common-factor tensor construction on the standard
SU(6) 15 carrier cannot realize these chosen dictionaries. This does not
exclude different placements, mass-selected subspaces or all SU(6) lifts.

`q_to_trivial_not_injective` proves that no invariant Q-to-trivial-copy map
is injective. `no_q_to_sign` proves the sign-target maps are all zero. If one
requires neutral-Higgs Yukawa flavor maps of this intertwiner type to be full
rank while S3 remains unbroken, neither sample meets that requirement. These
are proved flavor-map statements, not a new complete physical Yukawa or
fermion-mass certificate; a model application must supply that correspondence.
Other Higgs actions or symmetry-breaking choices are not tested here.

In particular, the zero-qque sample cannot be called a protecting model merely
because it passes gauge preservation. Other B1 families, full all-degree
support, realistic masses and the actual UV radical remain unverified.

## Exact computational supplement

The standard-library [signed-orbit check](../../../tools/su6-twisted-protection/check_s3_qque_tensor.py)
enumerates all six permutations and the ordered or symmetric Q-pair basis.
With a single sign factor the computed ordered invariant dimension is nine,
but the symmetric invariant dimension is zero. With two sign factors both
are eighteen. The single-factor Q/sign overlap is zero. These finite counts
are supplementary computations, not Lean finrank theorems or imported premises.
They illustrate why checking a raw tensor alone would misclassify the negative
sample before statistics is imposed.

## Consequence for further search

A practical sequence is: certify SM normalization, test common-factor
witnesses, compute the actual statistical tensor Hom when those witnesses
fail, then check realization and any declared Yukawa/full-rank requirements.
The common-factor stage is a sufficient nonzero test; only the actual tensor
stage supplies a complete selected-qque verdict in these samples.

There is now an SM-gauge-preserving coefficient-level zero example, but it
does not yet supply an admissible protecting SU(6) input. Any next candidate
must change the failed realization/flavor-map conditions, not just repeat
this zero test. Full SU(6) classification and new outer/antilinear foundations
remain outside this bounded endpoint.

See [verification](verification.md). No pins, axioms or audit exceptions
change; no master integration or push is authorized.
