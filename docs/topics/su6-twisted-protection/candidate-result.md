# Charge-Reversing Candidate: A Light-Spectrum Obstruction

## Result

A proposed ordinary complex-linear residual transformation which sends the
chosen hypercharge probe to its inverse cannot coexist with the positive SM
dual-index target in the covariant model. This rejects a specified candidate
behavior before the Lorentz/BNV Hom calculation. It constructs no protecting
solution and does not exclude every noncommuting SU(6) symmetry.

## Mathematical Argument

[CovariantCharacterObstruction](../../../Math/RepresentationTheory/CovariantCharacterObstruction.lean)
proves character invariance under the supplied automorphism action. Residual
covariance makes local(g) and local(alpha(h)(g)) similar; cyclicity of trace
removes the residual transformation. On a finite-dimensional carrier,
`Representation.char_dual` evaluates the dual character at the inverse.
Thus alpha(h)(g)=g^-1 forces zero dual index at g.

[ChargeReversingCandidate](../../../GUT/SU6/SelectionRules/Models/ChargeReversingCandidate.lean)
applies this to the actual mass radical using its derived covariant action.
`no_positive_target` excludes a positive-generation dual target whenever its
one-generation dual character is nonzero at that probe. No UV-support-to-light
inference or new mass-invariance hypothesis is inserted.

## Actual SM Probe And Dictionary

[HyperchargeReversalProbe](../../../Physics/StandardModel/Spectrum/HyperchargeReversalProbe.lean)
uses the existing actual `ExactSMSpectrum.generation`, not an arbitrary target
label. On the hypercharge circle its character is proved to be

```text
6 z + 3 z^(-4) + 3 z^2 + 2 z^(-3) + z^6.
```

These are the existing all-left-handed 6Y conventions: Q, u_R dual, d_R dual,
L and e_R dual, with dimensions 6,3,3,2,1. The computation follows the proved
species hypercharge actions and product-character rule. At the proved Circle
element z=i the character and inverse character differ nontrivially (16i).
Gauge singlets have zero dual gauge index and do not change this witness.

`no_sm_positive_target` accepts a homomorphism from the SM gauge-cover product
to the actual unbroken group K, and an explicit character dictionary matching
the supplied one-generation K target to the actual SM generation along it.
It does not require the covering product to embed injectively into SU(6).
The physical embedding and dictionary remain application inputs. Merely naming
a representation SM is insufficient.

## Exact Scope

The candidate condition specifies reversal at this probe, not a fully
constructed outer automorphism, its lift to UV matter, or a vacuum solution.
Any fully constructed candidate with this behavior and the dictionary is
excluded. No classification of SU(6) automorphisms is assumed or proved.

Ordinary complex-linear transformations are being tested. Anti-linear CP,
spacetime symmetries, or actions not reversing this probe are not covered.
The subsequent [conjugated-reversal test](defect-result.md) also excludes
reversal up to a supplied conjugation in K. Other normalizing actions and
general non-split gauge extensions remain unclassified.

A protecting Hom-zero solution cannot be claimed for a candidate that already
fails its light-spectrum condition. The existing exterior bridge is retained
for a later candidate that passes this test. Full Lorentz/BNV support, quantum
exactness and all-degree protection remain open application obligations.

## Verification

Strict transitive audits cover the generic character lemmas, actual SM probe,
and SU(6) application. The topic overview records focused/full builds and
layout/link checks. Only the three standard Lean axioms are allowed.
