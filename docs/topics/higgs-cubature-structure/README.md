# Structural Higgs Cubature Proofs

- ID: `higgs-cubature-structure`
- Status: complete; all three families verified and integrated into master
- Working branch: `refactor/higgs-cubature-structure`
- Integration target: `refactor/proof-memory-audit`
- Parent exception: bounded child of the proof-memory audit; later chain integration into master was explicitly authorized
- Authorization: completed one-family pilot, then user-directed extension to both remaining families

## Current Result

All three complete ordered moment identities now have structural proofs. The
transverse family uses tensor symmetry and Gram contractions with factor four;
the second collinear family transports the first through wave/node permutations.
All 420 old entry types are exactly preserved. Full build, strict audits,
source/API/reference checks and generators pass.

The remaining two families and their entire dependency closure compile in
327.052 seconds versus 1,547.397 seconds in the matching retained actual-compiler
baseline (78.9% shorter). Resident memory remains about 3.72 GiB. The candidate
contains 92 fresh compilations and zero ordinary project-cache reuses; the
baseline is explicitly historical. This is a proof refactor with unchanged
formulas, caller premises and physical scope.

The complete topic is integrated through its recorded parents into master.
[Merged-state verification](../source-api-compatibility/master-integration.md)
records the structural audits, original consumers and compatibility checks.
The measurements below retain their original before/after checkpoints.

- [Three-family proof](remaining-results.md)
- [Remaining-family verification and measurements](remaining-verification.md)
- [Frozen resumed plan](remaining-plan.md)

## Pilot Result

The complete first-collinear moment identity now follows from tensor symmetries
and three Gram contractions. All 140 old entry types are preserved. The full
build, original strict audits, public API/reference checks and source replay pass.
The measured dependency-closure compilation time falls from 417.906 to 174.705
seconds; maximum resident memory remains about 3.72 GiB. The unchanged data module
sets that peak. Other families remain outside this pilot.

- [Proof and compatibility result](results.md)
- [Measurements and verification](verification.md)

## Frozen Pilot Endpoint

Replace the first collinear family (`r = 1`, 72 configurations) with a structural
proof of the existing exact fourth-moment identity, for every ordered wave and
direction index. Preserve `raw`, `count`, `gram`, `factor`, `expected`, all existing
names/statements/hypotheses, dependency pins and original strict axiom/import gates.
Other families (`r = 0,2`) and namespace/directory policy remain outside this pilot.

The result must derive the moment shape from proved symmetries and then determine
its coefficients from exact Gram contractions. It must not merely call the old
35 full moment certificates or combine them into one large kernel decision.
Small exact certificates for node reindexings, phases and phase-invariant Gram products
are permitted; all are checked in Lean, never imported as Python premises.

## Pilot Plan And Needed Interfaces

1. Freeze old family source hashes and measure its 35 moment modules and shared
   local dependencies with the isolated profiler. Compile sources explicitly;
   distinguish measured local artifacts and external pinned package caches.
2. Prove a rank-four tensor lemma using coordinate-sign cancellation, coordinate
   permutations and a Hadamard diagonal constraint. Contracting its three paired
   components gives a three-by-three linear system; in dimension four, the
   72-node normalization yields the existing coefficients `5,-1,-1`.
3. Supply exact reindexings of the existing collinear nodes for coordinate
   permutations and one Hadamard transformation, plus a phase-covariant pairwise Gram
   identity whose products are constant. Prove bijections, fourth powers of phases and the required tensor
   symmetries. Do not assert a finite group order, generation or full-group
   invariance as an external premise.
4. Connect the structural identity to the existing first-collinear entry points.
   Retain old helper routes as small derivations if needed for compatibility;
   update the generator to reproduce accepted sources. Register any new library
   sources and strict audits in Math.lean.
5. Measure the new family including all new structural/certificate dependencies.
   Compare source checks, enumerated obligations, time and resident/virtual peaks.
   Verify old declaration types, generated-source consistency, existing Higgs
   audits, a complete ordinary build, layout and source/API/reference checks.
   Record exact bounded source changes without relaxing an audit predicate.

## Pilot Resources And Stops

One compiler at a time, two compiler threads, 16 GiB virtual address space,
540 seconds per invocation/build stage, core dumps disabled. Keep existing proof
options and axiom allowlists. Inspect peaks of 6 GiB resident or 14 GiB virtual.
No dependency upgrades, custom axioms, sorry, audit exceptions or higher limits.

Success means a checked structural proof for the complete first-collinear family,
working original consumers, explicit comparable measurements and a verified
commit. Source file count may stay stable when compatibility wrappers remain;
report computational certificates separately from forwarding proof files.

A scoped feasibility stop is valid if a required symmetry is false, or if the
route cannot be completed within these proof/resource gates without a new group
classification foundation or a changed premise. Diagnose the obstruction, retain
checked existing proofs and report remaining work; do not silently expand into
the other two families. No merge or push is part of the endpoint.

## Sources And Evidence

- [Existing construction and exact endpoint](../higgs-quartic-four-completeness/results.md)
- [Existing complete moment theorem](../../../Math/Algebra/Waves/HiggsFourWaveCubature.lean)
- [Existing sign cancellation](../../../Math/Algebra/HiggsFourWaveCubature/SignControl.lean)
- [Existing generator](../../../tools/derivative-literature/generate-higgs-cubature.py)
- [Profiler and measurement scope](../proof-memory-audit/README.md)
- [Verification and results](verification.md)

This is an exact algebraic proof refactor. It adds no literature theorem premise
and does not extend the physical or interacting-model scope of the Higgs theorem.

## Verified Design Correction

Initial exact diagnostics show that normalization by a common fourth root of
unity can change each quadratic Gram value by a sign. The raw Gram matrix itself
is therefore not a constant of all normalized nodes. Its products are constant,
which is exactly what fourth-moment contractions need. The pilot proves the
common Gram sign, its square-one law and the resulting constant products; no
public premise, endpoint or resource limit changes. Coordinate swap and Hadamard
reindexings and phase-covariant Gram identities pass Lean kernel certification.
The structural moment theorem and its 140 compatibility entry points pass all
recorded acceptance gates. This design correction changes no public input.
