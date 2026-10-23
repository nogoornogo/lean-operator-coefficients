# Li Printed Basis-Conversion Matrix Certificates

## Result

The printed complex coordinate matrix (4.38) is invertible, with an explicit
two-sided inverse and rank six. The first four highlighted rows of (4.41)
and (4.44) are bases of `Fin 4 → ℂ`; their full matrices have rank four.
These are exact coordinate-data certificates, not new differential EFT
completeness theorems.

Sources: [certificate](../../../../../Physics/StandardModel/Operators/BaryonOne/Inputs/LiBasisMatrixCertificate.lean),
[strict audit](../../../../../Physics/StandardModel/Operators/BaryonOne/Inputs/Audit/AuditLiBasisMatrices.lean).

## Inputs And Citation Role

[Li et al., 2201.04639v2](https://arxiv.org/abs/2201.04639v2) supplies the
transcribed data: (4.38), PDF p.33; (4.41), p.34; (4.44), p.36. The matrices
were checked visually in the PDF. The source is not an assumed Lean theorem:
the algebraic conclusions are proved from the entries independently.

All spaces are explicit finite complex coordinate spaces. `convertedBasis`
additionally accepts an independently supplied linear equivalence from the
six-coordinate space to a target module. It transfers coordinate bases; it
does not establish that target's identification with physical operators.

## Proof Structure And Normalization

`conversion` implements the six right-hand sides of (4.38). Its inverse uses
the printed factors of 1/4, 2 and the complex unit. `matrix38_apply` identifies
the separately transcribed matrix action with this map. Its surjectivity proves
`rank38 = 6` without numerical rank computation.

`synthesis41` synthesizes the first four printed rows. Its inverse explicitly
recovers their coefficients. `synthesis44` exchanges the second and third
coordinates, as required by the printed row order. Mapping `Pi.basisFun`
through these equivalences produces `basis41` and `basis44`. The row-agreement
theorems prove these are precisely the highlighted rows. Each full row span
contains a basis, so is the whole coordinate space, yielding ranks four.

## Applications And Boundaries

Given an independently proved coordinate dictionary for actual operators,
these certificates validate the invertibility/rank step of the indicated
alternative-basis argument. They do **not** verify the Fierz, derivative,
EOM/IBP or amplitude identities that give the matrix entries. In particular,
the zero ninth row of (4.41) is checked as data, not derived as an EOM relation.
No ABC4EFT output was executed, and no general p/y/m/j construction is claimed.

## Verification

The persistent audit checks the transitive axiom dependencies, permitting only
`propext`, `Classical.choice`, `Quot.sound`, and rejects model-layer imports.
Commands and outcomes are recorded in the
[topic](../../../../topics/li-remaining-scope-audit/README.md).
