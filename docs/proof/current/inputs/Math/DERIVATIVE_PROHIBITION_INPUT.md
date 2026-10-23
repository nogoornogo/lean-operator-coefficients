# Derivative Input Prohibition Conditions

[`Math.DerivativeProhibition`](../../../../../Math/RepresentationTheory/Jets/DerivativeProhibition.lean)
adds necessary-condition tests to the existing common derivative input.
The [topic results](../../../../topics/derivative-prohibition-input/results.md)
give the declaration map, actual controls and precise limits.

For the actual relation quotient, scalar action and nontriviality give
prohibition iff some group element detects the scalar character. A guarded
version also covers the zero quotient. Alternatively, explicit source
semisimplicity gives the no-common-irreducible criterion. An indexed-family
version combines these tests without claiming a decomposition or enumeration.
Zero derivative degree agrees with the published nonderivative criterion
before EOM. Its signatures are preserved.

Adding stable relations embeds the new coefficient space in the old one;
prohibition passes forward and allowance backward. Selected-input prohibition
implies vanishing of all global coefficients on that target. The reverse
requires actual restriction surjectivity. An explicit unipotent fixed-line
counterexample proves that the extension premise is material.

Actual quadratic IBP/free-EOM controls establish nonzero and zero sources.
The existing Lorentz scalar input additionally yields a necessary parameter
condition: a global coefficient nonzero on phi cubed requires zero coupling
in box phi + lambda phi cubed. Existence at zero coupling and whole-model
classification are not asserted.

See the [algebraic assumptions](ASSUMPTIONS.md#derivative-input-necessary-conditions),
[scalar assumptions](../Physics/assumptions/derivative-prohibition.md) and
[verification](../../../../topics/derivative-prohibition-input/verification.md).
