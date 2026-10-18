# Joint source expressions and actual finite support

The complete pure-color word iff now composes with all three independent
SU2 actions and finite source sums. This is an actual algebraic interface;
the remaining actual SM species/core and generation adapters are still
required for original endpoint 2.

## Proved interface

[`SU2TensorWordSupport.equivalence`](../../../Math/RepresentationTheory/SU2TensorWordSupport.lean)
constructs the entire decomposition of an arbitrary symmetric-power tensor
word. A path stores two child paths and a Clebsch--Gordan index. The degree
of a path is the proved Clebsch--Gordan degree; no multiplicities are counted.
Target occurrence is exactly existence of a path with the requested degree.
Scalar support is existence of a path ending at zero.

[`JointColorSpinWord.allowed_iff`](../../../Math/RepresentationTheory/JointColorSpinWord.lean)
retains color, weak, left spin and right spin together in a single tensor
word. It regroups the entire word before separating independent groups.
Its right side is the conjunction of the actual positive color diagram
criterion and three finite SU2 path conditions. It never substitutes
specieswise singlet permission for compatible coupling.

[`JointSourceExpression.decomposition`](../../../Math/RepresentationTheory/JointSourceExpression.lean)
constructs the actual finite sum for any expression built from joint atoms,
source products, tensor products and the zero source. Each branch choice
remains joint through all four labels. `allowed_iff` and `forbidden_iff`
then use only finite choices, positive color diagrams and SU2 paths.
The zero source has an empty choice type, needed for exterior overflow.

[`JointSourceDuality.equivalence`](../../../Math/RepresentationTheory/JointSourceDuality.lean)
normalizes actual contragredients into the same syntax. Its color dictionary
uses actual symmetric/kernel duals and evaluation biduality; each SU2
factor uses its own proved self-duality. No color self-duality is assumed.

[`JointSourcePresentation`](../../../Math/RepresentationTheory/JointSourcePresentation.lean)
stores an actual source equivalence and composes it under sums, tensors,
duals and group restriction. Atom maps insert proved scalar units.
[`RestrictedColorRestriction`](../../../Math/RepresentationTheory/RestrictedColorRestriction.lean)
proves restriction of the actual color kernels; inverse images in dual
factors are handled with the homomorphism inverse law. Color and spin
placement helpers retain the actual independent group coordinates.

## Scope

These theorems use no Weyl, branching, irreducibility-of-color or numerical
rank/multiplicity input. Every primitive color/SU2 support premise is
proved. A presentation-based consumer explicitly requires its stored source
equivalence; the actual SM adapters must construct those presentations.
The generic syntax iff does not claim those remaining adapters are finished.

Next: normalize the existing complete signed core branches into these
presentations, compose actual generation/species reductions, and reattach
Higgs/hypercharge/q/l conditions. See the [plan](joint-composition-plan.md)
and [verification](joint-composition-verification.md).
