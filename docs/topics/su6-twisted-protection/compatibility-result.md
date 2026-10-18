# Remaining Input Validation: Compatibility And Spectrum Ambiguity

## Necessary Condition For Non-Reversing Candidates Too

[DualIndexCompatibility](../../../Math/RepresentationTheory/DualIndexCompatibility.lean)
proves invariance of the entire dual-index function

```text
J_a(g) = character_a(g) - character_dual(a)(g)
J_a(alpha(h)(g)) = J_a(g).
```

Covariance preserves character and an automorphism preserves inversion, so the
same holds for the dual character. This uses actual representations, not a UV
weight-support inference.

[TargetIndexCompatibility](../../../GUT/SU6/SelectionRules/Models/TargetIndexCompatibility.lean)
applies that identity to the actual mass radical. If its index equals n times
a supplied target index with n>0, cancellation over the complex numbers gives

```text
J_target(beta(h)(g)) = J_target(g).
```

`no_positive_target_of_mismatch` rejects any supplied candidate/probe violating
this condition, including non-reversing actions. The SM-cover specialization
accepts the existing actual-SM character dictionary and a checked image
`beta(h)(cover(g)) = cover(g')`; unequal actual SM indices at g and g' exclude
the positive target. No injectivity of the covering product is assumed.

This is a necessary condition, not a classification or an existence theorem.
A candidate passing it still needs the actual field dictionary and residual
coefficient-Hom calculation. No new concrete non-reversing SU(6) action is
constructed or rejected by merely stating the mismatch test.

## Full Spectrum Does Not Follow From The Gauge Index

The generic Math module constructs an added one-dimensional trivial summand,
proves identical dual index and different character, and excludes a full
representation equivalence. It also constructs `a + (a + dual(a))`: a charged
vectorlike pair cancels in the dual index.

[DualIndexAmbiguity](../../../Physics/StandardModel/Spectrum/DualIndexAmbiguity.lean)
specializes the vectorlike construction to the actual `ExactSMSpectrum.generation`:

| Gauge representation | Character at identity / complex dimension | Dual index |
| --- | --- | --- |
| SM generation | 15 | J_SM |
| SM generation plus a generation and its dual | 45 | J_SM |

The equal-index theorem holds at every gauge element. Different identity
characters prove these representations are not equivalent. Thus the positive
one-generation *gauge index* alone does not identify even the charged full
spectrum needed for a species/Lorentz/BNV dictionary. This demonstrates a
logical limitation of that premise, not that every admissible SU(6) model has
extra light fields. No SU(6) representation, mass, VEV or residual realization
for the enlarged example is asserted. No claim about sufficiency or ambiguity
of the separate residual-resolved target is made here.

## Which Remaining Conditions Are Closed?

- The necessary all-probe index compatibility of an actual candidate is proved;
  testing its premise still requires a supplied beta and SM dictionary.
- Derivation of a full light-field dictionary from the gauge index alone is
  refuted at the gauge-representation level. It cannot be silently used to close
  the missing Lorentz/BNV support input.
- Actual UV matter/scalars, vacuum/mass realization, the full or supported
  light-field equivalence, Lorentz covariance, BNV-support preservation and
  residual-Hom zero remain candidate-specific obligations. These inputs are
  not currently instantiated together in this topic.

The [bounded plan](compatibility-plan.md) is complete after its checks. No
protecting model, general automorphism/extension classification or physical
proton lifetime is claimed. The next concrete model must specify how extra
vectorlike light content is excluded or included in its operator carrier;
that choice must be verified against its actual mass radical.

## Verification

Strict transitive audits cover 5 Math, 4 Physics and 3 GUT declarations, using
only `propext`, `Classical.choice`, `Quot.sound`.

- `lake build Math.RepresentationTheory.Audit.AuditDualIndexCompatibility
  Physics.StandardModel.Spectrum.Audit.AuditDualIndexAmbiguity
  GUT.SU6.SelectionRules.Audit.AuditTargetIndexCompatibility`: passed, 4,027 jobs.
- Final focused Physics build: passed, 3,757 jobs, after removing warnings.
- `lake build`: passed, 6,575 jobs on final source state, no warnings.
- `node tools/layout/check-layout.mjs`: 1,248 modules passed.
- `node tools/docs/check-links.mjs`: 511 files, 3,352 local inline links,
  85 heading fragments, zero errors.
- `git diff --check`: passed; theorem hypotheses and new source diff reviewed.

Initial redundant
simp warnings were removed without relaxing linting or changing hypotheses.
Pins and audit allowances remain unchanged; no master merge is authorized.
