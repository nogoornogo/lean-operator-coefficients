# C5 Input and Current Checkpoint

This is the preceding partial checkpoint, superseded by the
[completed result](results.md). Statements below describe that earlier stop.

The actual one-flavor Weyl/Higgs input, its generated/component equation
connection and the printed current dictionaries are proved. The intended
one-coordinate equivalence for the entire selected coefficient space
remains unproved. The topic reaches the foundational-interface stop of the
[contract](plan.md); this is a partial C5 result.

## Proved input and density

[WeylHiggsInput](../../../Physics/FieldTheory/Jets/WeylHiggsInput.lean)
uses the full exterior/polynomial jet algebra with independent component
labels `Bool × Fin 2` in each factor. Odd fields carry the actual left/right
SL(2,C) actions and integer hypercharges +6,-6; Higgs/dual fields carry the
existing global covering-SM action with charges +3,-3. Directions transform
contragrediently to Pauli vectors in signature (+---). Color acts trivially
on this lepton/Higgs source.

Both massless Weyl equations and the four free Higgs equations generate
the full unbounded two-sided differential closure. IBP adds the linear
divergence range. Multiplication is not added to the IBP relations.
`seed_stable`, `stable` and `grade_stable` prove actual-group stability.
The selected space is the entire mixed grade (2,4,1), with the preimage of
all full-source relations. Hypercharge balance is not an extra selection
assumption.

[WeylHiggsRelations](../../../Physics/FieldTheory/Jets/WeylHiggsRelations.lean)
compares every generated odd Euler component and every embedded generated
Higgs Euler component with the corresponding component seed. Their spans,
full differential closures and combined relations agree. The generated
presentation is the union of the two computed Euler families, not a claim
that an additional mixed Lagrangian AST has been constructed. Global and
selected coefficient equivalences have both inverse laws and preserve every
evaluation. The previous arbitrary-product current conservation and
symmetric-current redundancy now hold on this combined input.

[WeylCurrentCovariance](../../../Physics/FieldTheory/Jets/WeylCurrentCovariance.lean)
proves that the existing ordered Pauli current transforms as a vector.
[WeylHiggsCurrent](../../../Physics/FieldTheory/Jets/WeylHiggsCurrent.lean)
proves that the Higgs bidirectional current transforms as a dual direction,
the Higgs norm is invariant and opposite lepton phases cancel. Their full
contraction, including factor i, is invariant under arbitrary elements of
the actual internal/Lorentz group. The apparent absence of an extra metric
in the original source formula is consistent with this vector/dual pairing.

[WeylHiggsSelection](../../../Physics/FieldTheory/Jets/WeylHiggsSelection.lean)
proves the density belongs to the actual whole grade, constructs its fixed
selected element and exposes a linear evaluation map. This map is not yet
proved injective or surjective.

## Convention and failure controls

[MinkowskiWeylCurrent](../../../Physics/FieldTheory/Spinor/MinkowskiWeylCurrent.lean)
defines the chiral block gamma matrices, proves their (+---) Clifford law,
and proves the ordered right-projector current equals the two-component
Pauli expression. Its raised reversed-current expression includes the
Grassmann minus sign. Formal barred/conjugate components are specified
independent generators. No star involution, physical reality or Hermitian
real dimension is inferred from these complex-linear identities.

The [raw probe](../../../Physics/FieldTheory/Jets/WeylHiggsProbeControl.lean)
has value i on the density, proving the raw density is nonzero. On an
explicit total derivative it has value 2, so it fails relation admission.
This separates a nonzero raw expression from nonzero quotient support.
The [commuting-domain control](../../../Physics/FieldTheory/Jets/WeylHiggsCommutingControl.lean)
proves every algebra homomorphism from this source to a commutative domain
kills every odd jet and therefore the density. In particular, replacing
the C4 scalar-wave substitution by a domain-valued mixed substitution
cannot construct the needed lower coefficient.

## Settled formal stop

The two routes were assessed against the actual source, rather than a paper
count or the candidate span:

- The tensor/evaluation route supplies current equivariance and its complete
  physical block dictionary. Its remaining lower witness requires a
  Grassmann-valued relation evaluation, or a nonmultiplicative graded tensor
  functional, with full unbounded EOM/IBP annihilation. The existing colored
  scalar-wave algebra homomorphisms fail by the proved commuting-domain
  control. Raw component extraction also fails by the proved divergence test.
- The finite route constructs an exact rational model of 4160 ordered
  monomials. Hypercharge and three Cartan weights reduce it to 896 and 56
  variables. Lie constraints, both Weyl equations and IBP have cumulative
  ranks 52,54,55, and the candidate is detected. This is an independent
  diagnostic. It does not supply the basis/source map, the full unbounded
  relation-preimage span equality, or the passage from Lie rows to the
  arbitrary actual group required by `FiniteDerivativeCertificate`.

Completing either route therefore requires an additional mixed graded
projection/relation or Grassmann-evaluation interface. The scalar moment
interfaces do not supply it. The contract's foundation stop is used here;
no unproved bridge is inserted as a theorem parameter and no paper count
is used to complete the result. This stop is not a counterexample to the
expected one-dimensional coefficient space or a persistent compiler failure.

Precisely, the open statements are injectivity of `WeylHiggsSelection.evaluate`
on all `WeylHiggsInput.selected.Coefficient` and an admitted coefficient
with value 1 on its candidate. A normalized inverse and dimension-one
theorem depend on both. The finite diagnostic is useful data for resuming
that foundation on this same topic; it does not certify either statement.

All three [literature checks](literature-validation.md) were still executed.
They certify the achieved density/convention/input connections and retain
the same completeness boundary. Full SMEFT, interacting gauge/Yukawa EOM,
arbitrary flavors, amplitudes, running and rates are outside the result.
