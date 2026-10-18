# Multiplicity Coordinates And Local Basis Conversion

## Frozen Roadmap-1 Endpoint

Refine each intrinsic isotypic block into finitely supported copies of a simple
statistics module, using the existing semisimple-module existence theorem.
The multiplicity index need not be finite. Transport the residual action to
these coordinates and prove the coordinate equivalence and inverse conversion
between any two choices. Individual copies are not claimed to be residual-stable:
residual symmetry can mix multiplicity coordinates.

For bounded finite local dictionaries, prove explicit conversion coefficients
from one normalized complete contraction/probe family to another, both inverse
laws, and compatibility with coefficient reconstruction. Keep discovery of a
local dictionary distinct from conversion of two proved dictionaries.

No new dimension, topology, dependency or literature assumption is permitted.
Noncanonical choice must be exposed; no canonical Li basis is asserted. Stop
after roadmap 1 and its checks. Roadmap 2 (Li conventions) and 3 (j-basis) await
a separate user decision.

## First Milestone

[MultiplicityCoordinates](../../../Math/RepresentationTheory/MultiplicityCoordinates.lean)
proves that each intrinsic block has simple-copy coordinates with an arbitrary
nonempty multiplicity index. Existence is proved by mathlib's semisimple
isotypic theorem, not supplied as an external assumption. A chosen linear
equivalence transports the full residual representation; conversion between
two choices is equivariant and has a proved inverse. Scalar-field residual
coefficients have an inverse Hom equivalence with explicit evaluation formulas.

[FiniteLocalBasisConversion](../../../Math/RepresentationTheory/FiniteLocalBasisConversion.lean)
gives the coordinate change between two independently normalized, complete
local dictionaries. Its forward matrix entries are `p i (w j)` and inverse
entries `q j (v i)`. Both inverse laws and equality of reconstructed coefficients
are proved for arbitrary residual flavor.

## Completed Roadmap-1 Result

[StatisticsMultiplicityCoordinates](../../../Math/RepresentationTheory/StatisticsMultiplicityCoordinates.lean)
constructs a chosen simple-copy presentation for every actual statistics block.
Its `chosenCoefficientEquiv` refines the existing block-Hom product to residual
Homs on those coordinates. Extraction, inverse reconstruction and the zero
criterion are proved. Alternative presentations have an explicit equivariant
coefficient conversion with an inverse, so the result does not depend on the
noncanonical choice. Residual symmetry may mix copies; no copywise invariance
has been silently imposed.

`FiniteLocalIsotypicCompleteness.characterMultiplicityEquiv` composes this with
the actual local/flavor character-sector quotient. It requires no additional
coordinate-existence assumption. The finite statistics group, nonzero cardinal
in the scalar field, commuting actions and local dictionary certificates remain
the existing inputs.

[Concrete conversion controls](../../../Math/RepresentationTheory/FiniteLocalBasisConversionControls.lean)
prove two normalized, exhaustive dictionaries on a two-dimensional trivial
local representation. The second dictionary consists of the sum and difference
of the first, with half-sum/half-difference probes. For arbitrary residual flavor,
the coordinate conversion is `(c0,c1) ↦ ((c0+c1)/2,(c0-c1)/2)` and its inverse
is `(d0,d1) ↦ (d0+d1,d0-d1)`. The generic inverse and reconstruction theorems
apply to these proved certificates. This is an algebraic control, not a new
physical-sector or Li-convention identification.

Roadmap 1 is complete within its frozen scope. These are noncanonical simple-copy
coordinates, not canonical scalar coordinates on `Hom_statistics(simple, block)`.
There is no finiteness restriction on multiplicity indices, no discovery of
new physical local dictionaries and no claim of full Li basis construction.
Roadmaps 2 and 3 are deferred pending the user's decision.

## Verification

The persistent [audit](../../../Math/RepresentationTheory/Audit/AuditMultiplicityCoordinates.lean)
contains 31 strict transitive checks. Final commands/results are recorded in
the [topic overview](README.md#verification). Focused and full builds passed on
stage 01; no warnings/errors or nonstandard axioms were found. Roadmaps 2 and 3
were not started, and the branch has not been merged.
