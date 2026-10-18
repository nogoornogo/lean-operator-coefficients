# SC-2: Mass Radical And Supported Signatures

Status: Lean-checked conditional endpoint. Concrete SU(5)-chain adapters and
the final positive/negative controls remain separate SC-3/4 obligations.
Preceding source checkpoint: `checkpoint 01`.

[ConjugationMassSource.lean](../../../Physics/StandardModel/Spectrum/ConjugationMassSource.lean)
uses namespace `GUT.StructuralConjugationMass` and no GUT application imports.

## Proved Endpoint

`selection_rule_obstruction` accepts the planned data without strengthening
them: a torus map j into an arbitrary group G, an actual finite-dimensional
unitary representation of `G x H`, the three actual conjugations, an invariant
symmetric mass on the restricted torus/H action, a positive finite-profile
family, singlet data, and an exact radical dual-character target.

Its conclusion is failure of `ForbidsEverySupportedPhysicalDeltaBOneOperator`
on the actual resolved radical spectrum. `exists_actual_signature_pair`
constructs neutral supported `qque` and `duql` signatures and actual nonzero
radical vectors at all fifteen chosen SM weights with their residual charges.

This is a sufficient criterion, conditional on the actual conjugations and
the specified target. No claim is made that arbitrary groups supply these
inputs, or that this criterion extends physical model coverage beyond the
already treated standard chain.

## Why The Mass Assumption Is Unchanged

`HasTarget` is an identity of the actual radical's dual trace with the target
evaluator. `source_target` derives the corresponding identity for the source
using `B.radical_dual_character_eq`. Only then does `profiles_compatible` use
SC-1. The conjugating elements need not preserve B or its radical, and no
invariance of the full radical character under their permutations is asserted.

`spectrum` is extracted from actual joint-character eigenspace multiplicities
by `Finsupp.comapDomain`. `chiral_spectrum` proves its dual target equality;
it does not identify the full light spectrum with the SM target or exclude
vectorlike extra modes. Positivity gives `exists_zeroMode` and
`chargesSupported`, which supply the operator consumer without a support premise.

## Verification

```sh
lake build Physics.StandardModel.Spectrum.Audit.AuditConjugationMassSource
lake build
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
git diff --check
```

Focused build: 3818 jobs; 11 strict transitive axiom checks passed. Full build:
5560 jobs. Layout: 544 modules, no errors. Documentation link and diff checks
passed before commit. New Lean files have no warnings; inherited warnings remain.

The persistent [audit](../../../Physics/StandardModel/Spectrum/Audit/AuditConjugationMassSource.lean)
rejects GUT application imports and permits only `propext`, `Classical.choice`,
`Quot.sound`. Besides checking the final consumer type, it transports radical
vectors to ambient E and checks both the joint eigenvector equation and
`B.form v w = 0` for every w. The positive generation field is also checked.

Existing proofs and dependency pins are unchanged. No full-gauge radical
tensor, fermionic quotient, interaction coefficient, amplitude, anomaly
cancellation, or proton lifetime theorem has been added.
