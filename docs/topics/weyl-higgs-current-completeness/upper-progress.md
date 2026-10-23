# Whole-Grade Upper Bound

This records an intermediate checkpoint. Its pending tasks are now discharged
by the [completed result](results.md); its check counts remain checkpoint evidence.

[WeylHiggsUpper.evaluate_injective](../../../Physics/FieldTheory/Jets/WeylHiggsUpper.lean)
proves injectivity of candidate evaluation on every admitted coefficient of
the entire actual mixed grade (2,4,1). Equal candidate values imply equal
coefficients everywhere. This completes the upper half of the
[resumed contract](completeness-plan.md); the normalized invariant lower
coefficient remains in progress.

The [preceding Lorentz reduction](reduction-progress.md) removes both odd
derivative allocations and controls opposite-chirality spinor tensors by
the inverse Pauli coefficients. The new
[internal Higgs controls](../../../Physics/FieldTheory/Jets/HiggsFirstInternal/Complete.lean)
derive all needed rows from actual internal group elements. The marked
quartic words have 80 commuting monomials, eight phase-zero coordinates
and two remaining invariant coordinates. Their six sparse rotation
identities and complete field-index case split are checked by Lean.
These counts are not completeness premises.

[Internal lifting](../../../Physics/FieldTheory/Jets/WeylHiggsInternalLift.lean)
derives the required internal invariance from the actual selected C5
input. It uses grade-certified primitives and requires no invariant linear
extension to the full jet algebra. The
[IBP relation](../../../Physics/FieldTheory/Jets/WeylHiggsInternalIBP.lean)
gives A+B=0 for the two internal coordinates. The
[candidate calculation](../../../Physics/FieldTheory/Jets/WeylHiggsEvenCoordinates.lean)
gives value 24i(A−B), using the exact Lorentz trace eight. A zero candidate
value therefore forces both coordinates and every whole-grade word to vanish.

The selected-source theorem uses an ordinary relation-annihilating linear
extension through the quotient image. Its invariance is derived only on
the selected grade. No rank, source-spanning, hypercharge-selection or
invariant-extension assumption is left to the final caller.

The [four-wave sum](../../../Physics/FieldTheory/Jets/WeylHiggsWaveSum.lean)
still supplies a full-relation functional with candidate value 384i.
Its arbitrary-group invariance is the remaining lower task. A separate
[multilinear field interface](../../../Math/Algebra/ColoredFirstJetFields.lean)
is checked for that connection. Injectivity alone does not prove that the
invariant coefficient space is nonzero or one-dimensional.

The focused builds and fresh extended strict inventories pass 665 transitive
declaration checks, with only the three standard logical axioms and the
existing import-layer restrictions. The serialized full `lake build` passes
7996 jobs. All accepted additions have no tactic/linter warnings; direct
mathlib imports retain the existing module-system advisories. The Higgs
certificate generator reproduces its checked sources exactly. Layout passes
for 2500 modules; topic navigation, portable metadata, local links and diff
checks pass. The literature coefficient endpoint remains pending.
