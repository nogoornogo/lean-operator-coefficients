# E6 SU(5) Coordinate Comparison

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Checked Result

**The bounded coordinate-comparison task is complete.** No compatibility
hypothesis or dimension-based choice of an intertwiner was added.

- [SU5Coordinates](../../../../../GUT/E6/Minuscule/SU5Coordinates.lean) gives the
  signed bijection, kernel-checked equality of all entries for the four
  raising/lowering/Cartan generators, and the standard Hermitian identity.
- [SU5ExteriorCoordinates](../../../../../GUT/E6/Minuscule/SU5ExteriorCoordinates.lean)
  identifies exterior matrix coefficients with actual two-by-two minors.
  Polarizing `exteriorPower.map` constructs the infinitesimal action and
  proves its Leibniz rule. The actual dual action has matrix `-X.transpose`;
  the existing SU(5) `ten` and `antifundamental` actions have the corresponding
  exterior/inverse-transpose matrices.
- [SU5ModelComparison](../../../../../GUT/E6/Minuscule/SU5ModelComparison.lean)
  constructs `actualModelEquiv` to the actual direct sum of scalar, defining,
  dual and exterior-power spaces. `actual_generator_comparison` intertwines
  all twelve complex generators. Separate theorems handle their compact
  `X`, `Y`, `H` combinations; `actualModelEquiv_hermitian` preserves the
  standard coefficient inner product. No Haar-averaged basis is substituted.

The signed basis sends model basis vectors to the following ambient rows
(zero-based); exterior pairs are in lexicographic order:

| Block | Ambient rows | Signs |
| --- | --- | --- |
| Two singlets | `0, 20` | `+, +` |
| Five | `12, 15, 17, 19, 22` | All positive |
| First dual five | `7, 5, 3, 2, 1` | `+, -, +, -, +` |
| Second dual five | `26, 25, 24, 23, 21` | `+, -, +, -, +` |
| Exterior square | `4, 6, 8, 10, 9, 11, 13, 14, 16, 18` | All positive |

`coordinate_grade` proves that the grade-one part has the `10 + bar5 + 1`
coordinate blocks, the grade-minus-two part `5 + bar5`, and grade four the
remaining singlet. This is an infinitesimal action comparison, **not yet an
all-group-element branching theorem**.

The exact polynomial identity
`exteriorMatrix (1 + t X) = 1 + t wedgeMatrix X + t^2 exteriorMatrix X`
is proved for arbitrary complex matrices and scalars. The quadratic term
is retained: no unjustified identification of an exterior group action with
its linear part is made. Analytic differentiation/integration is not claimed.

## 2. Inputs and conclusion

### Frozen Task

The user approved a concrete coordinate-comparison implementation after the
[bounded route decision](../../../../topics/e6-global-topology/decisions/E6_DIRECT_BRIDGE_DECISION.md). Its consumer is the
future actual SU(5) action on the compact E6 candidate's 27 coordinates.

Use the A4 chain of E6 nodes `[5, 4, 3, 2]` in the pinned matrix conventions.
Compare with `1 + 1 + 5 + bar5 + bar5 + wedge^2(5)`, with ordinary dual action
`-X.transpose` and the exterior-square Leibniz action. Construct the signed
basis map explicitly; do not assume an intertwiner or identify modules by
dimension alone.

The finite deliverable is:

1. A bijection and signs for all 27 basis coordinates.
2. Equality of the four raising, lowering and Cartan matrix actions, with
   the exterior block tied to the actual exterior-power functor.
3. Preservation of the fixed standard Hermitian form, a persistent axiom
   audit, regression build and milestone commit.

Stop at these results, or document a precise failed comparison. No group
integration, exponential compatibility, faithfulness of a group map, exact
center, simple connectedness or physical target inhabitant is included.
This task does not establish an E6 selection-rule theorem or change any
existing theorem's hypotheses.

## 7. Sources and verification

### Verification and Stop

The [persistent audit](../../../../../GUT/E6/Audit/AuditSU5Coordinates.lean) checks 29
declarations against `propext`, `Classical.choice`, `Quot.sound`, and includes
negative/sector controls for dual signs and the repeated dual blocks.
Targeted build: 3870 jobs, 29 reports; no new-module warnings.

```sh
lake build GUT.E6.Audit.AuditSU5Coordinates
lake build
```

Full regression results are recorded in [historical milestone record](../../../../topics/e6-global-topology/checkpoints/e6-sources.md).
No Python output, external LLM, new axiom or dependency change is trusted.
The coordinate table is embedded in Lean and checked against the pinned
matrices. Reconstructing an exploratory JSON file is not required to build.

The agreed coordinate stop checkpoint was reached. Its next missing input was the actual
continuous injective group homomorphism into `compactIdentityComponent`,
including represented-exponential compatibility and subgroup membership.
Neither that map, its faithfulness, a named simply connected compact E6
identification, nor a positive-target 27 physical model is proved here.

The subsequent, separately scoped [group-map result](E6_SU5_GROUP_MAP.md)
now closes the continuous injective map, represented exponentials and
actual group restriction. Global identification and the positive-target
model remain open; this coordinate milestone itself is unchanged.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
