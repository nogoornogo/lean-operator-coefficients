# E6 Direct-Bridge Decision

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../proof/README.md).

See the [proof-document conventions](../../../proof/TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Outcome

This section records the decision at `checkpoint 01`. **Subsequent approved work
has closed the finite coordinate/generator comparison**, including the
Hermitian identity and actual exterior/dual modules; see
[the coordinate result](../../../proof/current/applications/GUT/E6_SU5_COORDINATES.md). Group-level exponential
compatibility, subgroup membership and the actual inclusion remain open.
The historical inspection below is not a claim that the new comparison
is still missing.

**E6-ENDPOINT-1 is complete as a bounded route decision; concrete
implementation is DEFERRED.** Both permitted routes were inspected once.
Neither currently provides the coordinate/action comparison needed to
construct the actual SU(5) map into `compactIdentityComponent`. No new
endpoint input was discharged. This is not a proof of impossibility, or
a claim that general Lie integration is mathematically necessary.

The first missing bridge is concrete representation compatibility, not
the center or fundamental group. Do not resume E6-0q or replace this
decision with another recursively expanded audit. All prior proofs remain.

## 4. Proof structure

### Inspected Routes

| Route | Checked reusable ingredients | First unavailable bridge |
| --- | --- | --- |
| Direct SU(5) action | `Matter.fundamental`, `Matter.antifundamental`, `Matter.ten`; continuous unitary realizations; finite-product SU(n) exponential generation | A constructed coordinate equivalence intertwining the intended SU(5) infinitesimal action with the retained generators of the actual E6 matrices, with the needed Hermitian compatibility |
| Existing Spin(10) action | Actual `SU5Inclusion`, `HalfSpin.representation`, `halfSpin_eq_exterior`, oriented `halfSpin_character` | An equivariant identification of the E6 `gradeSpace` blocks with these actual Spin/SU(5) modules; neither dimension 16/10/1 nor the separate Spin character supplies it |

Relevant source boundaries:

- [UnitaryMatter](../../../../GUT/SU5/Representations/UnitaryMatter.lean) explicitly
  does not assert that its unitarized coordinates are the original basis.
  Conjugating an action by an arbitrary linear equivalence does not establish
  unitarity for the E6 matrices' fixed standard Hermitian form.
- [D5Blocks](../../../../Math/LieGroups/E6/Minuscule/D5Blocks.lean) proves invariant coordinate
  subspaces and dimensions, not a representation equivalence to compact
  Spin(10). `gradeSpaceEquiv` is a coordinate restriction map, not that bridge.
- [SU5ExteriorAction](../../../../Math/LieGroups/Spin/SU5ExteriorAction.lean) identifies the
  actual Spin lift with an exterior action on its own space. It does not
  identify that space/action with the E6 grade-one coordinate block.
- [SpecialUnitaryGeneration](../../../../GUT/SU6/Embeddings/SpecialUnitaryGeneration.lean)
  gives two compact exponentials for every SU(n) element. It still needs
  compatibility between the represented exponentials and the target matrices.
- [ContinuousEmbeddingRegularityBridge](../../../../GUT/SU6/Embeddings/ContinuousEmbeddingRegularityBridge.lean)
  supplies generic `unitsGenerator`, `eq_expUnitHom_unitsGenerator` and
  `compactOneParameter`. They can classify an already constructed continuous
  one-parameter action, but do not supply its missing E6 matrix comparison.
- [MatrixLieGroupNormalizer](../../../../Math/LieGroups/Matrix/MatrixLieGroupNormalizer.lean)
  requires conjugation preservation of the real algebra; the checked
  exponential criterion is reusable once the concrete generator comparison
  has actually been proved.

Pinned-source inspection also checked nearby TauCeti exterior-power action
and one-parameter classification APIs. No direct E6/Spin coordinate
intertwiner was found in the inspected E6 modules. This is a scoped source
finding, not a formal theorem of nonexistence.

### Exact Missing Input

The desired group-level output for the *candidate* is an actual injective
continuous homomorphism `SU5.StandardModelEmbedding.TargetGroup ->*
compactIdentityComponent`, with the chosen SM chain explicitly composed.
Only then can the existing
[`StandardChain.ContinuousModel.selection_rule_obstruction`](../../../../GUT/Common/StandardChain/StandardChain.lean)
be specialized. Its mass and light-target assumptions stay unchanged.

For the inspected exponential route, first construct a continuous action
on the actual 27 coordinates and prove that, for every compact SU(5)
direction `X`, its represented exponential is `exp (D X)` with
`D X` in `compactMatrixLieAlgebra`. A signed basis matching the raising,
lowering and Cartan actions is a possible way to calculate `D`; no such
matching is assumed, generated or certified by this checkpoint. One must
also prove faithfulness. An arbitrary dimension-based basis equivalence
or a hypothesized compatibility field is not sufficient.

The unresolved coordinate comparison is a new concrete proof effort.
An end-to-end bounded implementation package was not established by this
pass, so its supporting lemmas are not automatically queued. Reopening
requires a fixed coordinate model, named comparison/transport obligations,
verification commands and an explicit stop checkpoint approved as a new
implementation scope, not another feasibility suffix.

Even a successful candidate-group inclusion would not by itself identify
the intended simply connected compact E6. That naming/global-form boundary
and an actual positive-target 27 inhabitant remain separately unproved.

## 7. Sources and verification

### Verification

Rebuilt the existing SU(5) matter, Spin branching, common standard-chain
and compact-candidate center audits: **4565 jobs / 245 axiom reports**,
using only `propext`, `Classical.choice`, `Quot.sound`. This verifies reused
ingredients, not either missing bridge. No Lean source or dependency was
changed; no new theorem or full-regression result is claimed. The last full
build remains E6-0p, 5470 jobs / 2384 reports.

```sh
lake build GUT.SU5.Audit.AuditMatterBranching GUT.Spin10.Audit.AuditSU5Branching GUT.Common.StandardChain.Audit.AuditStandardChain Math.LieGroups.E6.Audit.AuditCompactCenter
```

The disposable log is `.lake/e6-endpoint-1-audit.log`. This record is the
persistent output of the completed decision, not a conditional Lean bridge.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
