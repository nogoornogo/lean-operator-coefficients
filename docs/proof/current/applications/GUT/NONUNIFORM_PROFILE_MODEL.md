# Actual two-charge SU(6) profile model

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Checked Construction

**LEAN-CHECKED: PROFILE-3c.** The actual source is two copies of
`15 + 2 bar6`. One has the trivial residual action, and the other has a
scalar character `chi` satisfying `chi(h^-1) = chi(h)`. Scalar multiplication
is unitary and commutes with the full continuous SU(6) representation.

`ScalarResidualSource` proves that the full residual-character refinement
preserves the scalar label and that its trace is `chi(h)` times the original
SU(6) trace. Append compatibility then computes the two-copy trace without
assuming any branching target for the new source.

The existing signed-character calculation for `15 + bar6 - 6` supplies the
SM part. The remaining `6 + bar6` contributions cancel in the dual index
because the residual character is self-inverse. Each of the five target
profiles is therefore

```text
single 0 1 + single (Additive.ofMul chi) 1.
```

`mass_hasTarget` proves this target for **every invariant symmetric mass**
on these canonical fields. `model` uses the checked continuous standard
geometry and zero mass to construct an inhabitant of `ContinuousProfileModel`.
The exact target is proved, not an added realizability hypothesis.

## 7. Sources and verification

### Concrete Audit

`nonuniform` specializes to the two-element residual group `Int.units` and
its nontrivial sign character. The kernel-checked controls establish:

- Each species has one neutral and one sign-charged generation.
- The profiles cannot equal the old pure two-generation fixed-charge target.
- For **each of the fifteen oriented SM weights**, both charges have a
  nonzero vector in the actual mass radical.
- The actual field space and zero-mass radical have dimension 54, not 30.
- The model has supported neutral delta-B-one signatures and cannot prohibit
  every such signature by its Abelian charge selection rule.

The example allows vectorlike zero modes. It does not give a pure SM light
spectrum, nonzero mass, full-gauge radical tensor, or decay amplitude.
The earlier nonlinear nonzero-mass 15-mode regression remains independently
checked. The final profile theorem is not restricted to order-two charges;
self-inverseness is used only in this particular realizability construction.

### Files And Verification

- [ScalarResidualSource](../../../../../GUT/SU6/SelectionRules/StandardBranch/ScalarResidualSource.lean)
- [NonuniformProfileModel](../../../../../GUT/SU6/SelectionRules/Benchmarks/NonuniformProfileModel.lean)
- [AuditNonuniformProfileModel](../../../../../GUT/SU6/SelectionRules/Audit/AuditNonuniformProfileModel.lean)

Targeted command: `lake build GUT.SU6.SelectionRules.Audit.AuditNonuniformProfileModel`.
Result: 4173 jobs, 26 axiom-bearing reports. Full regression: 4392 jobs,
1437 reports, only `propext`, `Classical.choice`, and `Quot.sound`.
Logs are ignored artifacts at `.lake/build/profile3c-targeted.log` and
`.lake/build/profile3c-full.log`. All pins and existing endpoints are unchanged.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
