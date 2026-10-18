# E6 Candidate Tangent Image

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Checked Result

**E6-0m is complete at the linear tangent level.**
[CompactTangent](../../../../../Math/LieGroups/E6/Minuscule/CompactTangent.lean) computes the
actual manifold differential of the smooth matrix inclusion at one.
In the constructed chart it is exactly the inclusion of the already
checked real-form subspace into the ambient matrices.

The theorem `mfderiv_compactMatrix_one` retains explicit tangent/model
casts. Its consequences prove injectivity of the differential and
`exists_tangent_matrix_iff`: a matrix is the image of a tangent vector
if and only if it lies in `compactMatrixLieAlgebra`. The canonical
continuous real-linear tangent/model equivalence is tied to this actual
differential, not just to the previously known dimension 78.

This milestone alone is a linear result. The subsequent
**[E6-0n](E6_TANGENT_LIE_ALGEBRA.md)** now proves the Lie-algebra isomorphism,
including the explicit geometric invariant-vector-field bracket comparison.

## 7. Sources and verification

### Bracket Bridge Audit

Pinned TauCeti contains the required prospective ingredients, and their
axioms are now kernel-audited, not only source-inspected:

| API | Checked meaning | Remaining application |
| --- | --- | --- |
| `lieMap` | Smooth homomorphisms induce Lie maps on left-invariant derivations | Bundle the candidate's actual inclusion into matrix units |
| `leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap` | The induced map is the identity differential under the tangent equivalences | Compare that unit-valued differential with the checked matrix differential |
| `TauCeti.Lie.groupLieAlgebra_units_ad_apply` | The tangent bracket on units is the associative commutator | Apply it to the actual matrix-unit inclusion |
| `TauCeti.Lie.unitsLieAlgebraLieEquiv` | Units' left-invariant derivations are Lie-equivalent to the ambient associative Lie algebra | Restrict the image to the checked real form |

Mathlib's `Units.contMDiff_val`, `Units.isOpenEmbedding_val`, and
`ContMDiff.of_comp_isOpenEmbedding` provide the corresponding smooth
units API. The Lie functor assumes finite-dimensional real model spaces;
the candidate and its matrix ambient space meet this condition. No
dependency update or new external tool is required for this bounded route.

**[E6-0n](E6_TANGENT_LIE_ALGEBRA.md)** has implemented this bridge and checks
the geometric bracket explicitly, without substituting the model-space
bracket by instance selection. Simple connectedness, exact center, global
E6 identification and integrated Spin inclusion remain separate, subject
to the retained foundations cost gate.

### Verification

[AuditCompactTangent](../../../../../Math/LieGroups/E6/Audit/AuditCompactTangent.lean) checks
seven project declarations and four pinned-library ingredients against
`propext`, `Classical.choice`, `Quot.sound`. Examples instantiate the
actual differential, injectivity, exact image and tangent dimension; the
global-exponential negative control remains imported.

Targeted: **4029 jobs / 103 reports** (11 new checks, 92 reused).
Full: **5466 jobs / 2359 reports** (2358 lists and one axiom-free report),
standard axioms only. Both new modules are warning-free; ten Python tests pass.

```sh
lake build Math.LieGroups.E6.Audit.AuditCompactTangent
lake build
python3 -m unittest discover -s tools/e6 -p 'test_*.py'
```

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
