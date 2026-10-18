# Dipole Completeness Results

## Proved Endpoint

For an arbitrary abstract residual group H and multiplicity representations
a on A and b on B, with B finite dimensional, the independently defined
ordered chiral sectors satisfy

```text
SectorB(a,b) x SectorW(a,b) ~= Hom_H(a,b) x Hom_H(a,b)
exists nonzero coefficient iff exists nonzero Hom_H(a,b)
```

[DipoleSMCoefficient](../../../Physics/StandardModel/Operators/DipoleSMCoefficient.lean)
proves `equivB`, `equivW`, `equiv`, `exists_nonzero_iff` and actual-field
transport `onFieldsB`/`onFieldsW`. The independent sectors are the entire
invariant functional spaces on ordered L/Ec/Higgs/strength tensor products.
They are not defined as images of assembly. Tensor products supply the
universal multilinearity in the four distinguished species.

The SM covering product, SL(2,C) action and integral hypercharges are explicit.
The all-left conjugate convention uses charges -3, +6, -3, 0. Color is trivial
on each participating species. `cancelCharges` proves cancellation on the
actual ordered tensor product; surjective group descent then removes the
inactive color and U(1) factors without losing invariants.

The Higgs has one residual-trivial copy. No source semisimplicity, residual
compactness, continuity or finite dimensionality of A is required for this
coefficient equivalence. Supplied actual-field identifications carry their
own model obligations; the theorem does not derive a vacuum stabilizer or
a light spectrum.

## Local Completeness And Reuse

- [Concrete triplet](../../../Math/RepresentationTheory/TwoComponentSymmetricTensor.lean):
  explicit symmetric two-component action and pair projection; the mixed
  coordinate is half the sum of the mixed tensor entries.
- [Symmetric-square equivalence](../../../Math/RepresentationTheory/TwoComponentSymmetricSquare.lean):
  the triplet is equivalent to the independently defined symmetric quotient.
- [Adjoint coordinates](../../../Math/RepresentationTheory/TwoComponentAdjoint.lean):
  equivalence with traceless two-by-two matrices and the conjugation law.
- [Triplet self-duality](../../../Math/RepresentationTheory/TwoComponentTripletDual.lean):
  a nondegenerate invariant metric identifies upper/lower adjoint coordinates.
- [Two-component uniqueness](../../../Math/RepresentationTheory/TwoComponentTensorUniqueness.lean)
  and [actual groups](../../../Math/RepresentationTheory/TwoComponentContractions.lean):
  a diagonal element and a nondegenerate mixer exhaust all maps from the
  doublet tensor square to the triplet, for actual SU(2) and SL(2,C).
- [Spinor contraction](../../../Physics/FieldTheory/Spinor/DipoleSpinorTensor.lean)
  and [weak contractions](../../../Physics/StandardModel/Gauge/DipoleGaugeTensor.lean):
  normalized and exhaustive chiral spinor, weak singlet and weak triplet
  contractions. `weakDualEquiv` proves the pseudoreal Higgs identification.
- [Ordered local sector](../../../Physics/StandardModel/Operators/DipoleLocalSector.lean)
  and [residual extraction](../../../Physics/StandardModel/Operators/DipoleCoefficientCompleteness.lean):
  invertible regrouping, local reconstruction, dual evaluation and bidual
  transport derive the residual Hom description.

The general extraction and transport helpers live in Math. Local uniqueness
is a parameter only in the reusable abstract theorem; both concrete dipole
channels discharge it. Existing external invariant factorization now needs
only additive monoids, since its proofs never use subtraction. The complete
qque build and its 41-check coefficient audit passed with this relaxation.

[Distinct-species reconstruction](../../../Math/LinearAlgebra/DistinctSpeciesBilinear.lean)
and [fermionic extension](../../../Physics/FieldTheory/Spinor/DistinctFermionCoefficient.lean)
show that an arbitrary ordered L/Ec bilinear coefficient extends faithfully
to an alternating mixed-species coefficient. Pure L/L and Ec/Ec terms vanish;
the alternating mixed sector reconstructs from its ordered restriction.
Bosons remain in the value module. No symmetry is imposed on the residual
L-to-E map and no four-fermion exterior power is used for the bosons.

## Flavor And Arbitrary Inputs

[DipoleFlavorSelection](../../../Physics/StandardModel/Operators/DipoleFlavorSelection.lean)
uses a supplied mu vector and electron covector. It selects the B and W
matrix elements separately. The proved necessary-and-sufficient condition is

```text
exists coefficient with nonzero selected pair
  iff exists k : Hom_H(a,b) with electron(k(mu)) != 0
```

This is stronger than testing whether the full Hom space is nonzero. Under
source semisimplicity, existence of any coefficient is equivalent to an
actual common irreducible constituent, reusing the same general criterion
as qque. Common overlap alone does not assert off-diagonal flavor violation.

An equivariant bridge with nonzero selected matrix element suffices for
allowed flavor violation. Conversely, a residual symmetry element with
different weights on the prescribed source vector and target covector
forces every selected coefficient to vanish.

For any input domain X and any map F : X -> Coefficients, including nonlinear
maps and restricted domains:

```text
exists nonvanishing input iff range F is not contained in ker selector
surjective F => allowed flavor component iff realized flavor component
one generated channel = z * bridge, z != 0, selected bridge != 0
  => the selected pair is nonzero
```

Surjectivity is used only in its named specialization. The last statement
is an explicit sufficient-condition interface: a model must establish the
generated-channel equality, including any cancellation. An unconstrained
matching function is not substituted by an independently variable Wilson
coefficient. The image criterion alone is not a concrete UV-model theorem.

## Exact Sample Controls

[DipoleControls](../../../Physics/StandardModel/Operators/DipoleControls.lean)
uses two flavors with trivial residual action. The identity map has zero
off-diagonal selector; an off-diagonal bridge has selected value one.
A coefficient family constructed with z squared has selected pair (z^2,0),
is not additive, and is nonzero precisely for z != 0. A constant zero
generation map does not realize the flavor component even though the full
sector allows it. These are exact Lean controls, not a UV model or a claim
that a particular loop produces this family.

## Verification And Integration

- Planning commit `checkpoint 01`; proof commit `checkpoint 02`.
- `lake build Physics.StandardModel.Operators.Audit.AuditDipoleCompleteness`:
  passed, 3548 jobs. The [persistent audit](../../../Physics/StandardModel/Operators/Audit/AuditDipoleCompleteness.lean)
  checks 50 declarations transitively, permitting only propext,
  Classical.choice and Quot.sound, and rejects model-layer imports.
- `lake build`: passed, 5905 jobs. Existing warnings replayed. The final
  focused dipole build produced no new-source warnings.
- `node tools/layout/check-layout.mjs`: passed, 854 modules.
- `node tools/docs/check-links.mjs`: passed; final result record checked
  317 Markdown files, 1940 local links and 33 heading fragments.
- `git diff --check` and staged diff check: passed.
- No `sorry`, custom axioms, literature theorem parameters or new audit
  exceptions were introduced. Dependency pins remain unchanged. CLI builds
  substituted for unavailable Lean LSP MCP.
- The final documentation update did not rerun Lean or redefine the proof
  baseline. Existing unrelated numerical/model scripts were not rerun;
  their definitions and tested model inputs were unchanged.
- No merge into master and no remote push. The branch is retained under the
  user-requested integration policy.

## Remaining Physical Boundaries

The endpoint chooses one complex chiral field-strength module. It does not
construct a real Lorentz two-form, a Hermitian Lagrangian or an all-degree
operator/EOM/IBP quotient. Hermitian conjugation and Warsaw normalization
remain coordinate conventions outside the displayed equivalence.

The flavor identifications are inputs, not derived mass eigenstates. The B
and W selectors are not a matched photon coefficient; their electromagnetic
combination can cancel. Thus none of these results is a necessary-and-
sufficient condition for an observed mu-to-e-gamma decay.

Concrete UV generation, matching/RGE, rates, experimental bounds, additional
Higgs multiplicities and a common qque/dipole model condition remain separate
extensions. The present result supplies a complete coefficient target and
exact interfaces with which to investigate those input conditions.

The unmerged [input-structure child topic](../clfv-dipole-input-structure/README.md)
now supplies finite mediator-path criteria with arbitrary nonlinear weights,
an exact fixed-input cancellation formula and a pathwise existence equivalence
under explicit isolating inputs. It does not derive model-specific matching.
