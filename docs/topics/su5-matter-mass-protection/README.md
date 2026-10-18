# SU(5) Qque Obstruction And Matter/Mass Conditions

- ID: `su5-matter-mass-protection`
- Status: completed
- Result type: shared physical common-copy theorem and checked SU(5) arbitrary-mass realization
- Historical working branch: `proof/su5-matter-mass-protection` (deleted after verified merge)
- Integration target: `master`
- Integrated topic endpoint: `checkpoint 01`
- Merge commit: `checkpoint 02` (stage 02, explicit user authorization)
- Planning date: stage 01

## Decision And Endpoint

Use SU(5) as the primary model. Transfer the reusable mechanism from
[the SU(6) scalar/block result](../su6-twisted-protection/generalization-result.md),
then determine which matter, mass and light-placement restrictions can be
removed. SU(6) is provenance and a comparison case; its deferred exploration
is not reopened. SU(N), Spin(10) and E6 are later applications, not current
deliverables.

The endpoint is a conditional nonzero SM-cover, residual-H and SL(2,C)
invariant physical qque exterior coefficient on actual participating light
fields, together with an explicit applicability ledger for the bounded
matter/mass extensions. It is not a universal simple-group no-go, a generated
Wilson coefficient or a proton lifetime result.

The user authorized autonomous work and branch creation. The bounded endpoint
has reached its recorded stop gate: SU(5) transfer and conditional mass
transport are proved, a nonzero orthogonal mass control is proved, and both
matter routes have a finite assessment. See [results](results.md) and
[verification](verification.md). General compensated flavor actions remain a new scope decision; no protecting model is claimed.
Master integration was explicitly authorized and completed at stage 02;
see the merged-state checks in [verification](verification.md).

## Existing Results And New Obligations

- [Georgi-Glashow exterior result](../georgi-glashow-exterior/README.md)
  already covers actual `n(10 + bar5)`, positive n, zero symmetric mass and
  a compact continuous internal centralizer action. Reuse it; do not present
  its existing physical exterior endpoint as a new result.
- [Neutral physical qque](../../../Physics/StandardModel/Operators/NeutralQqueExterior.lean)
  already constructs a nonzero alternating coefficient from genuine species
  characters and neutrality, and transports it through representation
  equivalences. Its pointwise factors need not be homomorphisms.
- New obligations are the actual SU(5) scalar/block adapter, removal of the
  specific mass formula through explicit light-field certificates, and a
  bounded assessment of multiple copies and vectorlike additions.
- A subspace coefficient does not automatically extend to all light fields.
  Whole-light claims require an equivariant projection/splitting and a
  nonzero exterior pullback certificate.

## Additional Authorized Mass Phase

The user requested further mass checks at stage 01.
[Mixed-mass plan](mixed-mass-plan.md) freezes independent species mass rows
on two tens and one dual ten, with common scalar residual action. Earlier
results retain their scope; the general compensated-flavor problem is not
reopened.

The additional phase is proved: [mixed-mass results](mixed-mass-result.md)
derive actual light species for arbitrary independent complex mass rows with
common scalar ten character, including partial and zero rows. Nonzero active
mass has radical dimension 15, and physical qque remains nonzero. This closes
the specified C2 mixed-kernel bridge, not the general C1 compensated action.

## Arbitrary-Copy Matrix Phase

The user authorized the arbitrary-copy/common-scalar continuation.
[Matrix-mass plan](matrix-mass-plan.md) freezes three independent rectangular
species matrices on p actual source tens and q dual-target tens, retaining an
untouched bar-five. [Matrix-mass result](matrix-mass-result.md) derives light
embeddings and nonzero physical qque for every matrix when q < p. A conditional
nonzero-kernel version handles other sizes. This removes the two-copy and
explicit-row restrictions; common chi and the species Dirac ansatz remain.

## Assumption-Removal Assessment

The user requested examining removal of the common character and species
Dirac ansatz. [Assessment](assumption-removal-assessment.md) distinguishes a
proposed normal-form classification of arbitrary invariant mass on the current
carrier, common non-scalar copy representations, and independent species
representations. This is a feasibility decision, not a new Lean theorem;
implementation requires freezing the selected new signatures.

## Invariant Normal Form And Non-Scalar Copies

The user authorized both removals from checkpoint `checkpoint 03` on the existing
branch. [Plan](normal-form-copy-plan.md) freezes the two-stage endpoint.
[Results](normal-form-copy-result.md) distinguish the arbitrary-invariant-mass
normal form with common chi from the common non-scalar copy theorem with
arbitrary equivariant species maps. The subsequently closed unification and
remaining full-light completeness and UV/global-group obligations are recorded in
[remaining connections](remaining-general-connections.md).

## Unified Arbitrary-Mass/Common-Copy Phase

Authorized continuation from `checkpoint 04`, frozen in [unification plan](unification-plan.md).
[Unified results](unification-result.md) derive the three residual-equivariant
species maps from arbitrary invariant symmetric mass on the non-scalar carrier,
then prove actual light-range physical qque nonzero for positive dimension
difference. The former unification obligation is closed; full-light and UV/global
bridges remain explicitly recorded.

## Supplied Target Unitarity Removed

Authorized continuation from `checkpoint 05`, frozen in
[target-unitarity plan](target-unitarity-plan.md). The
[result](target-unitarity-result.md) derives an equivalent unitary target
internally, transports actual kernel splits back, and proves the arbitrary-B
physical endpoint on original participating ranges without supplied target
unitarity. Compactness and joint continuity remain. No algebraic-only or noncompact extension was part of that phase.

## Algebraic Common-Copy Phase

Authorized continuation from `checkpoint 06`, frozen in
[algebraic-copy plan](algebraic-copy-plan.md). The [result](algebraic-copy-result.md)
uses source semisimplicity for arbitrary H, with no target semisimplicity,
topology, compactness, continuity or unitarity. Actual common kernel splits
and original participating-range physical qque nonzero are derived, including
arbitrary invariant symmetric mass through the unified normal form. No
unrestricted nonsemisimple theorem is claimed.

## Pure Algebraic Copy Carriers

Authorized continuation from `checkpoint 07`, frozen in
[carrier plan](algebraic-carrier-plan.md). The [result](algebraic-carrier-result.md)
removes the remaining norm/inner-product carrier interfaces from the named
arbitrary-B source-semisimple endpoint. Its inputs now match the requested
finite-dimensional complex representation statement, with no H topology or
metric invariance. Earlier analytic consumers remain checked.

## Model-Independent Physical Bridge

The [shared result](model-independent-result.md), frozen in
[its plan](model-independent-plan.md), extracts actual mass-square realization,
light-range membership, restricted action and physical qque exterior nonzero
into Physics without SU(5) imports or a fixed unified matter carrier.
The SU(5) adapter derives the realization for every invariant symmetric B and
consumes the shared arbitrary-mass theorem. New models must prove the same
structural interface; a group embedding alone does not establish it.

## Current Stop And Remaining Boundaries

The authorized normal-form/common-copy and unification phases, including target-unitarity removal and the algebraic extension, reach their recorded endpoints. General
compensated-copy flavor actions, different residual characters on the two tens
and additional matter irreps remain separate scope decisions. Failure of a
common UV-copy certificate is not physical qque vanishing; for the new family
the source-derived mixed embeddings directly prove nonvanishing. No general
matter/mass classification or all-BNV protection test was completed.

## Verification

Focused builds, 73 strict transitive axiom checks, serialized full `lake build`,
layout/link/diff checks and the exact mass/qque controls passed. See
[verification](verification.md). Pins and axiom allowances are unchanged.
The additional phase passed 95 strict transitive axiom checks and its own
focused/full checks in the same verification record. The latest normal-form/common-copy phase passed 115 strict transitive checks
and its focused/full verification. The original plan's documentation-only
checkpoint remains in [plan](plan.md). The unified phase adds 27 strict
transitive checks and its own focused/full verification.

The target-unitarity removal passed 89 extended strict transitive checks and
its focused/full verification; the unchanged older theorem signatures retain
their preceding checkpoint evidence.

The algebraic phase passed 83 strict transitive checks across shared Math/Physics
and model audits, with its own focused/full verification.

The pure-carrier relaxation passed 70 model transitive checks and full
repository verification; the shared algebraic kernel proof is unchanged.

The model-independent phase adds 22 strict transitive checks, rejects shared
model-layer and original SU(5)/SU(6) imports, and passes the serialized full
build and repository checks. Its original-mass SU(5) realization is checked
as a direct consumer of the shared theorem.
