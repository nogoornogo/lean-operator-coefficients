# Actual Q core sources in the joint support interface

Every actual Q and conjugate-Q **single-generation core** exterior degree
now has a joint source expression, with the color, weak and two independent
spin actions retained. This applies the existing complete core decompositions
to the new positive support interface; it does not yet classify every
three-generation mixed content.

## Actual statements

[`SMQJointPresentation.positive`](../../../Physics/StandardModel/Operators/SMQJointPresentation.lean)
and `negative` construct presentations for the actual retained core species
0 and 5 at every natural exterior degree. `positive_allowed_iff` and
`negative_allowed_iff` include any weak Higgs constituent degree m:

```
Allowed (Invariants (actualCoreExterior n tensor weakSymmetric m))
  ↔ JointSourceExpression.Supports (constructedPresentation n m).expression
```

The right side contains only finite joint branch choices, positive color
contraction diagrams and three SU2 paths. It has no unknown Hom, kernel,
matching equivalence, multiplicity or rank. The source equivalence is
constructed, rather than supplied by an application.

The core has capacity twelve. The universal presentation handles all lower
and complementary degrees by the existing exact maps and perfect exterior
duality; overflow is represented by the proved zero source. The conjugate
family uses the proved actual tensor/dual comparison, preserving the
independent right spin. It does not identify the two spin groups.

## Construction

- `SU3DoubleSpinJointAtoms` places every concrete color and weak/spin atom
  at its actual retained group coordinate.
- `SU3DoubleSpinLowerPresentation`, `CubicPresentation` and
  `QuarticPresentation` turn the existing complete lower sources into
  finite joint expressions.
- `ColorWeakJointAtoms`, `FifthPresentation` and `SixthPresentation`
  retain the color/weak slices and their independent spin labels. No
  cancellation, character or branching premise is introduced.
- [`SU3DoubleSpinAllPresentation`](../../../Math/RepresentationTheory/SU3DoubleSpinAllPresentation.lean)
  assembles every degree, all complementary duals and the capacity-zero
  cases before the actual Physics core transports are applied.

The presentation interface was weakened to require only an additive monoid
and complex module on the input. Its stored equivalence still identifies
that source with the same actual joint expression. This avoids unnecessary
additive-group instance comparisons; no mathematical hypothesis was added.
Explicit coordinate group types also avoid unfolding representation data
while Lean infers a projection.

No numerical rank/multiplicity certificate, raised Lean limit, changed pin,
Weyl premise or new external mathematical input is used.

## Remaining endpoint

The full original endpoint 2 still requires the U/D and lepton core
presentations, actual three-generation/species composition, and the final
Higgs/hypercharge/q/l consumer. Q18 of the three-generation field is not a
single-generation core exterior degree; this result does not silently
substitute the latter for the former.

See [joint composition plan](joint-composition-plan.md),
[positive color coupling](colored-positive-coupling-results.md), and
[verification](q-joint-presentation-verification.md).
