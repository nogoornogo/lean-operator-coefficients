# Full Yukawa Space And Vacuum Evaluation

- ID: yukawa-full-space
- Status: completed
- Checkpoint detail: closed at revised endpoint; numerical coupling completeness deferred.
- Result type: kernel-checked exact five-dimensional mass image; external full-space candidate.
- Working branch: `proof/yukawa-full-space`.
- Integration target: `master`.

## Frozen Scope

On stage 01 the user revised the endpoint to retain the checked full
fixed-vacuum mass image, spectra and evaluation quotient, and defer the
SU(6) coupling dimension 22, kernel dimension 17 and concrete coupling
decomposition. None of these deferred results is assumed. Integration of
the completed milestones is authorized before starting the separate general
vacuum-evaluation/protection topic. The original scope below is historical.

Keep actual SU(6) matter 15 + 2 bar6, the existing symmetric-form scalar,
zero bare mass and specified vacuum. First produce reproducible exact
character and coordinate calculations of the full commutant and its vacuum
evaluation image. Supply independent checks and mutation controls. Scripts
are untrusted evidence, never a premise of a Lean theorem.

The long-term endpoint is a kernel-checked full coupling basis and the light
spectra of its evaluations. The immediate gate is an exact finite certificate
and identification of the interfaces needed to transport it to the existing
analytic representation. If that transport needs a separate foundational
theorem, document it rather than silently assume it or claim completion.
No potential minimization, new scalar choice, dependency changes or axioms.

### Direct Realization Milestone

Continued from checkpoint `checkpoint 01` using full-group equivariant flavor maps,
not an assumed Lie-to-group bridge. Five actual Yukawa directions, their
vacuum formula and independence are now proved. See
[direct realization and verification](direct-realization.md). This establishes
a five-dimensional subspace of generated masses. The subsequent
[finite-stabilizer upper bound](stabilizer-upper-bound.md) proves this is the
ENTIRE image. The full 22-dimensional coupling classification remains open.
No new analytic representation-theory foundation was introduced.

## Existing Interfaces

The [bounded existing-API test](api-feasibility.md) confirms the elementary
split and Schur interfaces, but does not reach the concrete SU(6) decomposition.
The remaining representation certificates require a separate proof milestone
or an explicitly approved literature input.

Latest milestone: [coupling kernel and evaluation quotient](coupling-kernel.md).
The [full residual decomposition](non-singlet-decomposition.md) and earlier
[dimension and singlet transport](spectrum-transport.md) remain proved.

- [All-coupling parameterization](../../../Physics/FieldTheory/Yukawa/YukawaClassification.lean)
- [Actual scalar and vacuum](../../../GUT/SU6/SelectionRules/Models/StandardSMUVYukawa.lean)
- [Branching coordinates](../../../GUT/SU6/SelectionRules/Models/StandardSMUVFields.lean)
- [Exterior branching](../../../GUT/SU6/Adapters/StandardSMExterior.lean)
- [Vacuum stabilizer](../../../GUT/SU6/SelectionRules/Models/StandardSMUVStabilizer.lean)
- [Completed two-coupling family](../yukawa-independent-blocks/README.md)

## Source Provenance

[Literature review and decision options](literature-review.md) records the
SU(6) tensor-product tables, Schur multiplicity formula and connected-group
intertwining theorem supporting an analytic derivation of 22 and hence 17.
The derivation is external mathematics; no literature premise has been adopted
and the full coupling dimension remains unproved in Lean.

The earlier 22-dimensional estimate used character arithmetic and Schur
orthogonality. Method reference (consulted stage 01):
[SageMath, The Weyl Character Ring](https://doc.sagemath.org/html/en/thematic_tutorials/lie/weyl_character_ring.html)
and [Weyl character rings reference](https://doc.sagemath.org/html/en/reference/combinat/sage/combinat/root_system/weyl_characters.html).
These document character decomposition and the sum-of-squared-multiplicities
calculation. They do not certify this repository's model or the number 22.
No Sage installation, external theorem premise or unchecked Lean input is used.

## Coordinate Results (External)

[Tool and conventions](../../../tools/yukawa/README.md). All arithmetic is exact
over integers/rationals. No sampling is used to compute the commutant or image.

| Quantity | Value |
|---|---:|
| Matter / symmetric scalar dimension | 27 / 378 |
| Raw endomorphism entries | 142884 |
| Weight-preserving unknown entries | 1704 |
| Simple-generator commutator equations / rank | 6780 / 1682 |
| Commutant basis size | 22 |
| Fixed-vacuum evaluation rank / kernel dimension | 5 / 17 |

The complete rational nullspace is constructed, checked against its equations,
and tested against all 30 off-diagonal generators. A separate weight-character
calculation gives irreducible dimensions/multiplicities 105:1, 15:2, 6:2,
84:2, 21:3, whose squared multiplicities sum to 22. Actual Dynkin labels of
the dual symmetric-form representation are included in the JSON output.

All 22 vacuum images span EXACTLY the five displayed mass directions, checked
by equality of spans, not dimension agreement alone. With coordinates ordered
as ten untouched modes, five triples and two singlets, the candidate mass is

```
0_(10) + five copies of [0 a b; a 0 0; b 0 0] + [u v; v w].
```

This fixed vacuum retains a larger symmetry than a generic SM-fixed vacuum.
Do not extrapolate the five-parameter result to another vacuum or Higgs choice.

## Kernel-Checked Block Algebra

[SmallSymmetricRank](../../../Math/LinearAlgebra/SmallSymmetricRank.lean) proves
over an arbitrary field: star-block rank 0 iff a=b=0, otherwise 2; singlet
rank 0 iff all three entries vanish, rank 1 iff nonzero with uw-v^2=0,
otherwise rank 2. `blockKernelEquiv` identifies the whole kernel of the
assembled coordinate map, and `block_nullity` proves its dimension for ALL
coefficients, not just sampled tuples.

| (a,b) | Singlet rank | Coordinate kernel dimension |
|---|---:|---:|
| nonzero | 2 / 1 / 0 | 15 / 16 / 17 |
| zero | 2 / 1 / 0 | 25 / 26 / 27 |

`nonzero_coefficients_rank_drop` proves dimension 16 at a=b=u=v=w=1,
an explicit control against classifying solely by which coefficients vanish.
The [actual radical](spectrum-transport.md) now has these dimensions; its
singlet factor is equivariantly split off. The
[non-singlet decomposition](non-singlet-decomposition.md) now identifies the
whole radical as a product of explicit irreducible residual representations,
for every allowed Y at this vacuum.

## Remaining Formal Connection

The entire vacuum image is now classified in Lean with no script premises.
The full 22-dimensional coupling classification remains open.
The [coupling-kernel theorem](coupling-kernel.md) now splits the ACTUAL full
coupling space as ker(evaluation) plus five coordinates, proves quotient
dimension 5 and gives a nonzero kernel witness. Dimension 22 is equivalent
to dimension 17 of that kernel; neither number is assumed or proved here.
Required interfaces for the full coordinate route remain:

1. Check the finite commutant basis and completeness in Lean, including
   row-reduction soundness rather than importing a computed rank.
2. Relate the finite generator action to the actual analytic group action.
   Commutation with Lie generators alone is not a proved full-group
   intertwining certificate in the current implementation. Existing
   `exteriorCoordinates_action` / `dualCoordinates_action` provide the group
   coordinate maps, not this remaining infinitesimal-to-group implication.

Kernel transport, the dimension formula and the full residual irreducible
decomposition are proved; they do not depend on completing items 1 and 2.

The direct realization bypasses step 2 for the five displayed mass directions,
not for all 22 couplings. The evaluation upper bound now uses a proved finite
subset of the vacuum stabilizer, bypassing that bridge for all vacuum images.
Do not assume the remaining full-commutant bridge or start unrestricted foundations.
The remaining boundary is formal completeness/transport, not a measured
computational explosion. This numerical endpoint is deferred under the revised scope.

## Verification

Original coordinate checkpoint: both script modes and all 8 tests passed;
7 strict SmallSymmetricRank axiom checks, full build (5852 jobs), layout
(801 modules), docs (303 files, 1838 links, 33 fragments) and diff checks
passed. Only propext, Classical.choice and Quot.sound were allowed.
Subsequent linked milestones record their own builds and audits; the latest
is [coupling-kernel verification](coupling-kernel.md). No pins, resource
limits or axiom exceptions changed. Scripts remain untrusted cross-checks.

Recheck and integrate the revised endpoint; retain the branch and do not push.
