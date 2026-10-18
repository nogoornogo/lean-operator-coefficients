# Frozen Proof Plan

## Inputs And Target

Work over complex vector spaces with specified linear residual actions of an
arbitrary abstract group H. The physical fields are the existing left-Weyl
quark doublet and lepton doublet, with three Q slots and one L slot. Their
species-scaling exterior sector is independently defined before assembly.

Finite-flavor specialization supplies bases indexed by finite types I and J
for Q and L. Separate quark and lepton flavor counts are allowed. The desired
unrestricted basis is for trivial residual action. For general H, the output
is a subspace of these coordinates cut out by explicit intertwining equations.

## Phase 1: Published Contractions And Local Statistics

Recover the qqql candidate from the pinned v2 PDF. Record its equation/page,
flavor projector or relations, slot order and local normalization. Prove its
interpretation as local multilinear contractions before exterior descent.
Keep operator/coefficient duality explicit when finite bases are introduced.

Derive the first-three-slot permutation action from `exchange01` and
`exchange12`. Determine all actual components and their multiplicities using
the existing Young/isotypic results where useful. Do not assume qqql is a
single mixed component. Account for repeated flavor labels and the raw
alternatization factor from the existing `1/6` ordered reconstruction.

Acceptance: the candidate contractions have proved coordinates in the existing
four-coordinate local dictionary, and all permutation signs agree with the
existing exterior equivalence.

## Phase 2: Nonredundant Finite Flavor Coordinates

Two permitted routes are an explicit solution of the finite exchange kernel,
or a decomposition using existing simple-copy/isotypic coordinates followed
by an explicit finite basis. Select the route after inspecting the local
representation. Helpers for finite combinatorics and coordinate inverses lie
within scope; a new general Schur-Weyl foundation does not.

Construct a finite index set B(I,J), coordinate extraction and reconstruction.
Prove both inverses on the independently defined exchange kernel, then compose
with `QqqlExteriorCompleteness.exteriorEquiv`. Prove every reconstructed basis
element agrees with the mapped published candidate, including projector
normalization where applicable.

For general H, transport its actual action to these coordinates and prove the
equivalence with the independent intertwining constraints. Matrix units are
admissible only after trivial residual action is proved.

Acceptance: an explicit equivalence with unrestricted coordinates for trivial
H action and a constrained coordinate equivalence for arbitrary H.

## Phase 3: Independence, Counting And Controls

Transport the coordinate basis to the physical sector and prove linear
independence and spanning. Derive the cardinality of B(I,J), hence the finrank
formula in terms of the two flavor counts. Literature counts are comparison
data, not theorem parameters. State conjugate-sector and Hermitian-conjugate
counting conventions whenever comparing totals.

Controls include no quark/lepton flavors, one quark flavor with arbitrary
lepton count, the existing neutral one-generation dimension one, and equal
flavor numbers two and three. Exact scripts may discover inverses or check
signs; Lean verifies the general claims. Include negative sign/normalization
controls when the semantic bridge is exercised.

Acceptance: the published candidate family presents the independently defined
sector, with both inverse identities and a general proved dimension formula.

## Verification And Documentation

Place shared helpers in Math and physical adapters in Physics, register new
modules in aggregates, and persist a strict audit. Run focused builds, strict
transitive axiom/import checks and `lake build`, then layout, links and diff
checks. Update the Physics assumptions ledger at verified milestones and write
a completed-result dossier on closure. Root README changes and master merge
require separate user direction.

## Investigation And Stop Conditions

Source recovery is one pass through the pinned paper PDF/TeX and its cited
author repository. Coordinate construction considers the two routes above.
Stop for a scope decision if the printed object requires derivative, EOM/IBP
or amplitude foundations, if essential new representation-theory foundations
exceed the existing interfaces, or if the proposed endpoint has a counterexample.

A mismatch in counts or signs first triggers examination of conventions,
projector normalization, conjugate counting and actual candidate definitions.
Retain the evidence and correct the statement; do not alter audits or assume
literature completeness to resolve the mismatch. ABC4EFT execution and new
computational dependencies are unnecessary for the paper-based endpoint.
