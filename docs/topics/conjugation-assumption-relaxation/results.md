# Assumption Relaxation: Results

Both weakenings hold simultaneously. The [topic](README.md) records scope,
milestones and integration; the [statement](../../proof/current/inputs/Physics/STRUCTURAL_CONJUGATION.md)
describes the current sufficient criterion.

## AR-1: Independent Positive Totals

Commit `checkpoint 01` adds
`FiniteChargeProfiles.exists_occupied_compatible_of_positive_totals` and
`exists_occupied_trivial_characters_of_positive_totals` in
[FiniteChargeProfiles](../../../Physics/StandardModel/Spectrum/FiniteChargeProfiles.lean).
They require only positive Q/down totals in addition to orbit compatibility;
the later mass theorem derives that compatibility rather than assuming it.
Old `Family`-based selection theorems wrap the new proof.

[AuditIndependentProfileTotals](../../../Physics/StandardModel/Spectrum/Audit/AuditIndependentProfileTotals.lean)
uses characters of `Multiplicative (ZMod 3)`, with multiplicity 2 at the trivial
charge for Q/up/electron and 1 for down/lepton. It proves no common total exists
and nevertheless constructs an occupied neutral charge assignment. This is a
finite coefficient test, not a complete quantum-consistent model.

Focused build: 3081 jobs; 4 strict transitive axiom checks. Full AR-1 regression:
5565 jobs. Layout: 549 modules.

## AR-2: Restricted Unitarity And Actual Modes

Commit `checkpoint 02` extracts
[RestrictedConjugationMassSource](../../../Physics/StandardModel/Spectrum/RestrictedConjugationMassSource.lean).
The namespace `GUT.StructuralConjugationMass.RestrictedUnitary` provides:

- `spectrum`, `spectrum_nonneg`, `chiral_spectrum`: actual radical coefficients
  with only unitarity of the `T x H` restriction.
- `exists_zeroMode`, `chargesSupported`: actual nonzero radical eigenvectors
  and coefficient support, using the exact dual target.
- `exists_actual_signature_pair`, `selection_rule_obstruction`: separate positive
  Q/down totals and the unchanged actual conjugations yield supported neutral
  `qque` and `duql` signatures and refute universal signature prohibition.

`HasTarget`, `source_target`, and `profiles_compatible` retain their original
names and types in the extracted file. They require neither ambient nor
restricted unitarity. The old
[ConjugationMassSource](../../../Physics/StandardModel/Spectrum/ConjugationMassSource.lean)
keeps its public theorem types and wraps the core. Its spectrum is definitionally
the same object, not merely a spectrum with equal dimension or index.

[AuditRestrictedConjugationMassSource](../../../Physics/StandardModel/Spectrum/Audit/AuditRestrictedConjugationMassSource.lean)
checks consumers with no `Family` or ambient-unitarity premise, actual ambient
vectors satisfying the zero-mass equation, spectrum compatibility, and a
conditional actual-mass endpoint for the unequal-total finite-residual target.
This consumer still requires actual matter and its exact target; it does not
establish existence of such matter by itself.

Focused new audit: 3820 jobs, 10 strict transitive axiom checks. The unchanged
old mass and standard-chain adapter audits passed (3928 jobs); the actual
15-dimensional chain benchmark remains valid through the new core.

## Final Gates And Limits

- `lake build`: passed, 5567 jobs.
- `node tools/layout/check-layout.mjs`: passed, 551 modules.
- `node tools/docs/check-links.mjs` and `git diff --check`: passed before integration.
- 14 new strict checks allow only `propext`, `Classical.choice`, `Quot.sound`;
  persistent import audits forbid GUT application dependencies in Physics.
- Existing unused-section-variable warnings remain in
  `Math/LinearAlgebra/FiniteBasisHilbertization.lean`. No new warnings.
- Dependency pins, the three conjugation identities, and E6 literature inputs
  are unchanged. Prior APIs and proofs remain available.

The positive-support, finite-dimensional, Abelian, invariant symmetric-mass and
exact dual-target assumptions remain. Unitarity has been localized, not removed.
No anomaly consistency, strictly wider physical model class, nonzero operator
coefficient, amplitude or proton lifetime is established. The third proposed
relaxation (only partial target information) was not investigated in this topic.
