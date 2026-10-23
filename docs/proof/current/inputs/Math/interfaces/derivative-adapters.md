# Derivative And Additional-Relation Input Adapters

The published derivative-free API is retained without source or signature
changes. These optional adapters add independently constructed relations to
an existing coefficient presentation. See the
[input recipe](../../../../../topics/derivative-interface-adapters/input-guide.md),
[result](../../../../../topics/derivative-interface-adapters/results.md) and
[verification](../../../../../topics/derivative-interface-adapters/verification.md).

| Module | Main interface |
| --- | --- |
| `Math.RepresentationTheory.Jets.DerivativeInterface` | Purpose-specific graded/full-EOM factories, common operations and invariant source-image selection |
| `Math.RepresentationTheory.Jets.DerivativeInterfaceControls` | Shared operations on the complete actual mixed IBP source |
| `Physics.FieldTheory.Jets.Scalar.Inputs.ScalarDerivativeInterface` | Packaged actual Lorentz scalar model and wave/cubic source selection |
| `Math.RepresentationTheory.Coefficients.MixedOperatorInput` | One mixed coefficient input and equivalence for all natural-number derivative degrees, including zero, with arbitrary direction actions |
| `Math.RepresentationTheory.Coefficients.RelationInputExtension` | Extra source relations mapped through a proved coefficient presentation, both inverse laws and nonzero/forbidden criteria |
| `Math.RepresentationTheory.Relations.FiniteLocalExtraRelations` | Explicit contraction input map, extra relation images and residual-Hom extraction/reconstruction |
| `Math.RepresentationTheory.Jets.JetInputAdapter` | Same public relation input, actual mixed jet divergence, inverse zero-grade compatibility and full polynomial EOM/IBP |
| `Math.RepresentationTheory.Jets.JetAdapterControls` | Complete actual mixed positive-grade source and its finite-local coordinate connection |
| `Physics.FieldTheory.Jets.Scalar.Inputs.ScalarInputAdapter` | Existing interacting scalar source, including the actual Lorentz action and cross-grade EOM relation |

Finite local coordinates retain their normalization and invariant-completeness
inputs. Arbitrary represented sources need stable relations, without requiring
finite dimension, averaging or a supplied complement. Additional EOM constraints
do not imply recovery of the unconstrained derivative-free source at degree
zero. Nonlinear EOM uses the full source unless a grading theorem is provided.
The strict public inventories cover all new definitions and theorems and
preserve the Math/Physics/GUT import boundaries.

For new derivative-side work use `DerivativeInterface.graded` or
`DerivativeInterface.equations` and their shared `P.coefficientEquiv`.
`MixedOperatorInput.coefficientEquiv` remains the lower-level uniform mixed entry.
The zero-degree source has proved equivariant inverse compatibility with the
original exterior/symmetric source even under direction mixing. Positive-degree
inputs and maps agree with the existing covariant jet interface. Nonlinear EOM
continues to use the whole source, so this uniform grading does not silently
impose homogeneity on equations.

`P.select V hV` pulls back the complete relation submodule and identifies its
quotient linearly with the actual image of V in the full quotient. Global
coefficients restrict compatibly. No extension of every selected invariant
coefficient, independent grading or invariant complement is inferred. The
nonlinear equations factory retains its commutative-algebra scope.
