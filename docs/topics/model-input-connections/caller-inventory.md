# Caller Obligations And Shared Construction

## Before Implementation

| Consumer | Existing model evidence | Repeated connection obligation |
| --- | --- | --- |
| SU(6) boundary amplitudes | Concrete embeddings/extractions, exact projector fixed spaces, gauge covariance, residual charges | Turn selected-image equalities into stable representations and both inverse maps; derive extraction covariance; retain the internal gauge/residual dictionary |
| Lepton-parity mass kernel | Explicit spectator pair and its mass radical, three-generation species, Weyl regrouping, nonzero Yukawa tensors | Turn radical membership and inclusion/extraction into the same stable representation interface; transport Weyl factors and coefficient evaluations |
| Local scalar/Weyl density | Actual invariant total density, Euler-span covariance and full equation relations | Reexpress/select the full input, derive relation preimages and coefficient/quotient roundtrips without termwise equation replacement |
| S3 qque sample | Actual noncommuting group action and statistics-correct coefficient | Instantiate shared field selection without an abelian-group constraint; preserve its existing coefficient witness |

## Frozen Shared API

Use the existing `Subrepresentation` as the stable selected-space object.
Construct it from equivariant kernels, arbitrary common fixed constraints,
subgroup restriction and coordinate changes. Construct its target equivalence
from an ambient inclusion, a left inverse and reconstruction on the selected
space. Derive extraction covariance on that space. No global equivariant
retraction is assumed. State the two-sided criterion separately from this
ambient sufficient constructor.

Interactions descend by composing actual intertwining maps, tensor/exterior/
symmetric maps and fixed-vacuum insertion. Existing coefficient naturality
provides the statistical quotient transport. The derivative adapter uses the
exact preimage of the full relation module under the supplied field/source
map. A model retains its own evidence relating the field substitution to the
jet and direction actions.

## After Implementation

| Consumer | Constructed facts replacing repeated connection work | Retained model-specific evidence |
| --- | --- | --- |
| SU(6) boundary | `ofMaps` constructs the three charged dictionaries and a separate exact neutral sterile dictionary for joint gauge/circle actions; `realized` derives right-sector stability; extraction covariance is automatic; Weyl/dual and coefficient/jet transports are shared; `atVacuum` recovers the old join exactly | Existing branching maps, exact selected-image proofs, source boundary signs, residual phases and fixed brane vector. Analytic mixed-mode admission remains separate. |
| Lepton-parity kernel | `massDictionary` reconstructs the exact radical equivalence directly from inclusion/extraction; common Weyl, mixed-degree and coordinate-jet factories apply to it | Actual spectator mass, its radical-membership theorem, five species/three generations, signed alphabet and nonzero Yukawa tensors. No SU(6) lift is supplied. |
| Local density | Generator dictionaries induce an actual all-order algebra equivalence; `pullAlong`, `pullEquiv` and `imageEquiv` derive exact relations, evaluations and recovery; paper comparison composes directly | The existing full density and actual Lorentz/direction representations; its independently proved density symmetry and paper component dictionary. The new map does not replace full EOM with termwise ideals. |
| S3 sample | The same kernel/inverse factory constructs selected fields and transports the nonzero ordered qque functional and its exchange identity | The original permutation/sign representations, positive tensor and obstruction to uniform flavor actions. |

No caller supplies a final selected-field equivalence, new branching result,
or relation-span equality for these constructions. The general derivative
entry still needs the existing complete relations and their stability, or a
model such as `StandardDensityAction.model` that derives them. Choosing bases
for actual finite carriers supplies syntax, not a spectrum hypothesis. The
old public definitions remain intact as compatibility and regression targets.
