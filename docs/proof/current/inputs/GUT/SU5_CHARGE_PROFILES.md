# Actual SU(5) residual charge profiles

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Checked Scope

**LEAN-CHECKED: PROFILE-3b.** For every ordinary Abelian unitary action on
the retained `n (10 + bar5)` matter, the five natural finite profiles are
derived from the full residual-character eigenspaces on the actual generation
spaces. Their totals are `n`; the three `10` profiles agree, as do the two
`bar5` profiles. The residual group need not be finite or topological.

The generic proof constructs the independent internal sum of character
subspaces, uses finite dimension to restrict to finitely many nonzero
subspaces, and proves dimension additivity. Repeated characters count the
entire eigenspace, not one selected vector. A character has positive
multiplicity exactly when a nonzero common eigenvector exists.

## 3. Definitions and conventions

### Fields And Tensors

Every occupied assignment produces the existing injective SM field maps
inside the retained matter. For `n > 0`, `supported_profile_tensors` combines
an occupied compatible assignment with the existing nonzero ordered `qque`
and `duql` tensors, preserving gauge and residual invariance. This does not
replace the field maps by formal coefficient support.

This remains a selection-rule statement, not a decay-amplitude calculation
or a Grassmann/Lorentz nonvanishing theorem. No new SU(6) source is inferred
from the SU(5) adapter.

## 7. Sources and verification

### Files And Audit

- [UnitaryCharacterProfile](../../../../../Math/RepresentationTheory/Characters/UnitaryCharacterProfile.lean)
- [ChargeProfiles](../../../../../GUT/SU5/SelectionRules/ChargeProfiles.lean)
- [AuditChargeProfiles](../../../../../GUT/SU5/Audit/AuditChargeProfiles.lean)

The audit rejects transitive SU(6) imports. Actual two-generation swapping
produces two occupied characters; a trivial action has repeated multiplicity
two; zero generations give zero profiles.

`lake build GUT.SU5.Audit.AuditChargeProfiles` succeeds (3906 jobs, 48
axiom-bearing reports including the prior matter-source audit). Full build:
4389 jobs, 1411 reports, only `propext`, `Classical.choice`, and `Quot.sound`.
Ignored logs: `.lake/build/profile3b-targeted.log` and `profile3b-full.log`.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
