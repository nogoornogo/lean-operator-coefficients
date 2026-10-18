# Invisible Inner Defect And Conjugated Probe Reversal

## Field-Level Inner Defect

For a supplied genuine covariant action U and a pointwise lift s implementing
its local automorphisms by conjugation, put

```text
C(h) = a(s(h)⁻¹) U(h)
d(h,l) = (s(h)s(l))⁻¹ s(hl).
C(h) C(l) = a(d(h,l)) C(hl).
```

[PointwiseInnerDefect](../../../Math/RepresentationTheory/PointwiseInnerDefect.lean)
proves this exact equality on the original carrier. Invertibility of C(hl)
also proves the necessary-and-sufficient criterion

```text
C(h) C(l) = C(hl)  iff  a(d(h,l)) = identity.
```

A normalized lift s(1)=1 with every represented defect trivial therefore
produces a genuine representation of H commuting with the local group action.
The lift itself need not be a homomorphism. A defect visible on the carrier
prevents the group law for this particular choice of removed maps; it does not
rule out another lift, another compensator, or a protecting physical model.
Centrality of a defect is not a premise proving its trivial action on matter.

[InnerDefectCandidate](../../../GUT/SU6/SelectionRules/Models/InnerDefectCandidate.lean)
exposes the criterion on the actual SU(6) mass radical. Here s takes values in
the unbroken group K and implements beta, not an arbitrary UV automorphism.
The resulting representation commutes with K. It is an algebraic representation:
continuity of an arbitrary pointwise s is not supplied or inferred. Neither
commutation with all UV SU(6), an exact light spectrum, nor the earlier UV-source
proton-charge obstruction follows from this construction.

This closes the earlier field-group-law gap only under the explicitly checked
invisible-defect condition. The previous result that *all* pointwise gauge
factors disappear after local coinvariants remains valid even when defects
are visible on fields.

## Reversal Up To Unbroken-Gauge Conjugation

[CovariantCharacterObstruction](../../../Math/RepresentationTheory/CovariantCharacterObstruction.lean)
now covers alpha(h)(g)=c g⁻¹ c⁻¹. Covariance preserves the character; a character
is constant on gauge conjugacy classes. Therefore the actual carrier's dual
index is zero at g just as for exact inversion.

[ChargeReversingCandidate](../../../GUT/SU6/SelectionRules/Models/ChargeReversingCandidate.lean)
extends both the general positive-target test and the actual SM-cover probe
test. With the existing positive actual-radical target and SM character
dictionary, a candidate sending the phase-i probe to an unbroken-gauge conjugate
of its inverse is excluded. Inner compensation of this form cannot evade that
test. The compensator c must belong to K. No general SU(6) outer automorphism
classification, anti-linear CP exclusion or VEV construction is asserted.

## Status Of The Remaining Cases

| Input pattern | Result of this phase |
| --- | --- |
| Pointwise inner lift with normalized, invisible represented defect | Commuting local-group representation constructed |
| Defect visible on actual light fields | This removed action fails its field group law; no universal model exclusion |
| Inversion up to conjugation in K | Excluded by the positive SM target/dictionary |
| UV lift outside K or genuinely different non-reversing coefficient action | Still requires a concrete candidate, light dictionary and Lorentz/BNV support |

The [bounded plan](defect-plan.md) is complete after its verification gates.
These are conditional tests; no protecting model, full Lorentz BNV-Hom zero
result, or proton lifetime is constructed. General non-split-extension or
SU(6) automorphism classification remains beyond the frozen scope.

## Verification

The focused command was `lake build
Math.RepresentationTheory.Audit.AuditPointwiseInnerDefect
GUT.SU6.SelectionRules.Audit.AuditInnerDefectCandidate
GUT.SU6.SelectionRules.Audit.AuditChargeReversingCandidate` (4,030 jobs).
Full `lake build` passed (6,569 jobs), with no warnings on final source state.
Layout checked 1,242 modules; Markdown links checked 509 files with zero errors;
`git diff --check` passed. Development associativity and explicit section-parameter
errors were corrected without changing the hypotheses.

Strict transitive audits
cover 4 inner-defect Math declarations, 3 covariant-character declarations,
3 actual-light-defect GUT declarations and 5 reversing-candidate declarations;
the existing 3 actual SM-probe checks are replayed. Only `propext`,
`Classical.choice`, `Quot.sound` are permitted. No pins or audit allowances change.
