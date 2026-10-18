# Standard SU(5) chain declarations

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. The common SU(5) chain
connects actual source and mass data to supported neutral signatures, with
retained SU(5) and canonical SU(6) adapters.

## 2. Inputs And Conclusion

The algebraic, continuous and scalar wrappers have distinct action/inclusion
premises; positivity and the exact radical dual target are retained.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Actual character spectra and index conservation derive profile compatibility and
zero modes; pullback and descent compare the model presentations.

### Composition Status

The retained SU(5) and positive canonical SU(6) conversions are checked
below. CHAIN-4 is checked separately in the
[standard SU(N) record](standard-su-n.md), with universal block inclusions
and an actual SU(7) positive-target example. No classification of arbitrary
ambient embeddings is claimed.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Shared Character and Mass Core

The CHAIN-1 declarations below are kernel-checked prerequisites. The actual
SU(5) source and ambient-group theorem are recorded in the later sections;
the [standard SU(N) specialization](standard-su-n.md) completes the
[roadmap](../../../../../topics/standard-chain-foundations/plans/STANDARD_SU5_CHAIN_PLAN.md).

| Module | Checked responsibility |
| --- | --- |
| `Math/RepresentationTheory/Characters/AbelianCharacterPolynomial.lean` | Integer `Finsupp` over complex monoid characters; faithful evaluation and dual involution |
| `Math/RepresentationTheory/Characters/UnitaryCharacterSpectrum.lean` | Actual nonnegative finite spectrum from full character eigenspaces, equality to trace, and nonzero eigenvectors |
| `Physics/FieldTheory/Mass/SymmetricMassIndex.lean` | Invariant radical, nondegenerate self-dual quotient, and exact dual-character conservation for arbitrary groups |
| `Physics/FieldTheory/Mass/AbelianMassSpectrum.lean` | Coefficient-level conservation, lower bounds, and actual zero modes from positive target coefficients |

The polynomial API retains the `GUT.AbelianActualSpectrum` namespace.
The algebraic mass API retains `GUT.InvariantWeylMass.SymmetricMass`.
Existing imports and declaration names remain available through the
legacy entry points; no old result was discarded.

`UnitaryCharacterSpectrum.spectrum` is constructed from the finite set of
nonzero full Circle-character eigenspaces. `spectrum_apply_complexCharacter`
identifies its coefficients with `UnitaryCharacterProfile.profile` (and
therefore with the full eigenspace dimensions). `spectrum_eval` proves
equality with `Representation.character` by additivity of trace across
the internal direct sum. Neither a spectrum nor an eigenbasis certificate
is an input. The Abelian group need not be finite or topological.

For an invariant symmetric complex bilinear form B and actual unitary
representation rho, `AbelianMassSpectrum.radical_dual_spectrum_eq` proves

```text
spec(rad B) - dual(spec(rad B)) = spec(rho) - dual(spec(rho)).
```

Given an evaluated source dual-character target p,
`coefficient_lower_bound` proves `p(chi) <= spec(rad B)(chi)`.
`exists_zeroMode_of_pos` constructs an ambient nonzero vector v satisfying
both `B(v,w) = 0` for every w and `rho(h)v = chi(h)v` for every h whenever
`p(chi) > 0`. `source_target_of_radical_target` supplies the same source
input from a light dual-character target. The mass can be zero, degenerate,
or nondegenerate. Positivity is essential for the **chosen orientation**;
a merely nonzero signed coefficient does not suffice.

The character conservation theorem itself needs no norm or unitarity;
those assumptions enter the actual finite nonnegative spectrum construction.
No gauge embedding, SM profile compatibility, or operator neutrality is
asserted by this generic mass module.

### Actual SU(5) Source

CHAIN-2 is checked for an actual finite-dimensional unitary representation
`rho : Representation C (SU(5) x H) E`, with arbitrary Abelian H. Separate
strictly commuting unitary actions produce this product representation via
`CommutingUnitaryActions.combined`; the two original actions are recovered
by restriction. No finiteness or topology on H is needed in this algebraic core.

| Module | Checked responsibility |
| --- | --- |
| `GUT/SU5/Embeddings/MaximalTorus.lean` | Determinant-one diagonal torus; actual SU(5) signed permutation conjugation |
| `GUT/SU5/Embeddings/PhysicalTorus.lean` | Surjective color/weak/hypercharge coordinates; equality to the actual SM embedding and physical integer exponents |
| `GUT/SU5/Branching/TorusCharacter.lean` | Rank-four normalized target evaluator, faithful joint weight/residual characters, Weyl and dual compatibility |
| `GUT/SU5/Branching/TorusCharacterSource.lean` | Actual trace and dual trace invariance; target Weyl invariance without source Laurent polynomiality |
| `GUT/SU5/SelectionRules/TorusMassSource.lean` | Source-derived profile equalities, actual radical coefficients and nonzero vectors, supported neutral signatures |
| `GUT/SU6/Branching/SU5TorusCompatibility.lean` | Exact equality with the old physical Fourier evaluator, isolated from the SU(6)-free core |

`HasTarget` specifies the exact **dual** character of the actual mass radical.
Its physical-coordinate formulation is equivalent, by torus surjectivity.
The mass need only be invariant on the torus times H; full-SM invariance is
neither assumed nor inferred here. `profiles_compatible` combines mass-index
conservation, actual Weyl conjugation, faithful target evaluation, and the
new `orbitCompatible_of_dual_invariant`. The old coefficient theorem remains
as a wrapper with its unchanged signature.

`spectrum` records the radical's full eigenspace multiplicities **at integral
SU(5) torus weights**. It does not assert that an arbitrary abstract source
has no other characters. `chiral_spectrum` gives the target equality on these
coefficients; positivity gives actual nonzero radical vectors.
`exists_actual_signature_pair` supplies qque/duql signatures with trivial
residual characters and actual vectors at all fifteen selected weights.
`selection_rule_obstruction` refutes universal charge prohibition. It does
not supply a general full-SM radical tensor, a nonzero coupling, or an amplitude.

The retained `n(10 + bar5)` endpoint is preserved and regression-tested:
it has stronger full-field/tensor conclusions, but narrower matter and
retained-spectrum inputs. Its conversion to the new radical-target
interface is now checked in the retained-model adapter below.

`AuditTorusMassSource` rejects transitive SU(6) imports and checks the raw
diagonal-shift ambiguity, a genuine odd Weyl representative, finite cyclic
charge separation, order-two weight/dual distinction, and rejection of
incompatible profiles despite correct species totals. The legacy evaluator
comparison is audited separately.

Verification at stage 01: targeted build 4031 jobs / 61 axiom-bearing
reports; full build 4407 jobs / 1499 reports. Only `propext`, `Classical.choice`,
and `Quot.sound` occur. Dependency pins and existing endpoints are unchanged.

### Ambient Pullback and Actual Inhabitants

CHAIN-3a is checked in `GUT/Common/StandardChain/StandardChain.lean`.
For any supplied homomorphism `i : SU(5) -> G`, `pullback` restricts the
actual `G x H` representation; `pullback_comp` proves compatibility with
further group homomorphisms. The algebraic `Model` needs no injectivity,
ambient faithfulness, or continuity. Its inputs are unitarity, an invariant
torus/H symmetric mass, a positive finite-profile family and exact dual
radical target. Its conclusions are derived profile compatibility, actual
supported qque/duql signatures and failure of universal charge prohibition.
`Model.ofSU5_spectrum` proves exact recovery of the CHAIN-2 spectrum.

`ContinuousModel` additionally requires an injective continuous inclusion
and jointly continuous ambient product-group action; pullback continuity is
proved. `ScalarModel` evaluates a jointly continuous equivariant mass family
at its fixed vacuum, preserves the exact bilinear form, and recovers an
existing mass through a constant-family constructor. Its
`toContinuousMassModel` accepts the same physical inclusion/action evidence.
Neither wrapper chooses a vacuum dynamically or proves its exact stabilizer.

`GUT/SU5/Branching/TorusMatterCharacter.lean` reuses the existing full-group
branching equivalences to prove that the actual unitary ten and anti-five,
with arbitrary independent residual characters q and r, have exactly the
fifteen-weight target character with `sectorCharges q r`. This is an identity
on the whole torus/H group, not a sampled equality. The small
`HilbertProductRepresentation` helper preserves the algebraic product action,
trace, inner product and joint continuity without unfolding concrete
unitarization constructions during every product proof.

`GUT/SU5/SelectionRules/StandardChainBenchmark.lean` constructs that
actual Hilbert sum, proves its exact target and zero-mass inhabitant, and
proves radical dimension 15. Continuous characters give a continuous model;
in particular the neutral action works for every topological Abelian H.
No nonzero mass or coupling is claimed for this example. The target theorem
also applies to any invariant mass on these same actual fields.

`AuditStandardChain` rejects transitive SU(6) imports and checks nontrivial
order-three charges, a continuous neutral model, and an injective SU(5)
inclusion into `SU(5) x C2` with exactly matching spectrum. The latter
illustrates ambient pullback without imposing a faithful ambient matter
action. Existing SU(5)/SU(6) endpoint audits remain in the full build.

Verification at stage 01: targeted build 4088 jobs / 92 axiom-bearing
reports; full build 4412 jobs / 1530 reports. All reports use only `propext`,
`Classical.choice`, and `Quot.sound`; dependency pins are unchanged.

### Retained SU(5) Model Adapter

`GUT/SU5/SelectionRules/RetainedChainSource.lean` converts every old
`MatterSource.OrdinaryAction H n`, including arbitrary generation mixing,
to an actual `SU(5) x H` action on the **same** Hilbert field space. Gauge
and residual restriction recover the original actions exactly. No scalar
action on the original field space is imposed.

`ExplicitMultiplicityTrace.trace_mix_action` computes the trace of a
multiplicity matrix times a constituent action. Combined with the actual
ten/anti-five trace and `UnitaryCharacterSpectrum.profile_eval`, this gives
`torus_character`: the actual restricted character equals the evaluator of
`FiniteChargeProfiles.target (ChargeProfiles.profiles R)` on every torus/H
element. `ProfileEvaluation` supplies the finite-profile target calculation.

`hasTarget` derives the exact dual radical target for **every** invariant
symmetric mass on this representation. `massModel` preserves any supplied
mass exactly and needs only `n > 0` beyond the old source. The retained-field
specialization `model` uses zero mass. `SymmetricMass.zeroRadicalEquiv`
identifies its radical equivariantly with the original field representation;
`zero_radical_spectrum` identifies its entire finite character polynomial,
and `spectrum_eq` proves exact equality of the common light spectrum with
the old finite-profile target. This full equality is stated for zero mass,
not inferred from equality of dual indices for general masses.

For continuous R, `continuousMassModel` and `continuousModel` construct
the physical wrapper and preserve the mass/model. No topology on H is
needed by the algebraic adapter. The old supported full-SM field maps and
invariant internal tensors remain available and are not replaced by the
common theorem's weaker signature conclusion.

`AuditRetainedChainSource` rejects transitive SU(6) imports. Its actual
order-two example swaps two ten generations, preserves the repeated
neutral anti-five coefficient 2, and gives two distinct occupied ten
charges and an actual nonzero odd-charge radical vector. Zero generations
give the zero spectrum. The audit also checks preservation of the actual
residual action and arbitrary supplied mass, and retains the previous
full-field/tensor audit.

Verification at stage 01: targeted build 3956 jobs / 80 axiom-bearing
reports; full build 4416 jobs / 1562 reports. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. No dependency pins changed.

### Canonical SU(6) Model Adapter

CHAIN-3b is complete for `ContinuousProfileModel.Model` and its evaluated
scalar-family models. Existing positive-generation legacy wrappers first
use `ContinuousProfileModel.Model.ofLegacy`. The stronger SU(6) embedding,
hypercharge-rigidity and independent flipped routes remain intact.

| Module | Checked responsibility |
| --- | --- |
| `GUT/SU6/Representations/UnitaryVirtualRestriction.lean` | Restriction commutes with actual Hilbert products, copies and positive aggregation, as bundled-field equalities |
| `GUT/SU6/Representations/ChargedAmbientRealization.lean` | Actual SU(6) x H realization of the charged summands; restriction exactly recovers the old canonical physical fields |
| `GUT/SU6/Embeddings/StandardSU5Inclusion.lean` | Continuous injective standard SU(5) block inclusion, factoring the legacy (-2,3) physical torus action |
| `Physics/FieldTheory/Mass/SurjectiveMassDescent.lean` | Invariant mass descent when an action factors through a surjective homomorphism; form and radical are preserved |
| `Math/RepresentationTheory/Characters/UnitarySpectrumRestriction.lean` | Character-polynomial restriction, and exact multiplicity recovery under surjectivity |
| `GUT/SU6/SelectionRules/Models/PhysicalChainSource.lean` | Descent to the SU(5) torus, transfer of the exact dual target, and full old/new spectrum equality |
| `GUT/SU6/SelectionRules/Models/CanonicalChainTransport.lean` | Constructed dependent-transport certificate, including a field isometry, mass compatibility and radical equivalence |
| `GUT/SU6/SelectionRules/Models/CanonicalChainModel.lean` | Automatic conversion of the old positive canonical models using their proved hypercharge pair |

`SU5TorusCompatibility.cover_surjective` compares the additive physical
torus times H with the determinant-one SU(5) torus times H. The individual
weight/charge characters match by `key_comp_cover`. This map is **not**
injective: the audit exhibits a nonidentity kernel point. No inverse chart
is assumed. Full spectrum equality follows from surjectivity and faithful
character evaluation, not merely equality of dual indices.

For an old model M, `CanonicalChainModel.model M` is an actual
`StandardChain.Model` on the lifted SU(6) fields. `fields_eq` uses
`M.hyperchargePair_eq_standard`, rather than adding the standard pair as
a new premise. `action_compatible` and `mass_compatible` compare the actual
field action and bilinear through `fieldEquiv`. `radicalEquiv` intertwines
the entire old physical group, with `radicalEquiv_apply` identifying its
map with the field isometry. `radical_character`, `radical_finrank`,
`mass_nonzero_iff` and `spectrum_compatible` retain the corresponding old
data; profiles and singlets are unchanged. The conversion certificate is
**constructed**, not supplied by a caller. It prevents costly unfolding of
canonical charge-sector spaces during later proofs and adds no axiom.

`scalar_mass_compatible` preserves the evaluated bare-plus-family mass.
It does not descend an arbitrary legacy scalar action through the torus
kernel. Likewise, `continuousModel` asks for continuity of the full lifted
product action: the old model has no topology/continuity input for H, so
that stronger property cannot silently be inferred. Neither qualification
changes the algebraic selection-rule endpoint or the old scalar models.

`AuditSurjectiveMassDescent` rejects transitive SU(5)/SU(6) imports and
checks a nonzero descended mass, exact recovered multiplicities, and a
nonsurjective restriction that merges two characters. `AuditCanonicalChainModel`
checks the noninjective torus cover and converts the existing nonlinear
nonzero-mass example (15 radical modes) and nonuniform two-charge example
(54 radical modes), preserving their full spectra and selection-rule
obstructions. The extra modes in the latter are not silently removed.

Verification at stage 02: targeted build 4256 jobs / 118 axiom-bearing
reports; full build 4426 jobs / 1612 reports. All scanned reports use only
`propext`, `Classical.choice` and `Quot.sound`. Dependency pins are unchanged.

## 6. Scope And Limitations

The generic endpoint is weaker than a full-SM radical tensor theorem; exact
full-spectrum comparisons require their additional proved character identities.

## 7. Sources And Verification

The [scope ledger](../../../inputs/GUT/ASSUMPTIONS.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.

### Compatibility and Audits

The old SU(6) spectator spectrum remains defined.
`AbelianActualSpectrum.spectrum_eq_unitaryCharacterSpectrum` proves it
equals the new spectrum for every old bundled actual unitary representation,
using faithful evaluation. This is exact polynomial equality, not a
comparison on sampled group elements.

`Physics/FieldTheory/Mass/Audit/AuditAbelianMassSpectrum.lean` rejects **transitive**
SU(5)/SU(6) imports and checks:

- An actual circle-character line and its positive zero-mass mode.
- A two-dimensional unitary action with a nonzero symmetric mass on the
  neutral line, retaining the positive-index chiral zero mode.
- A negative dual coefficient with no eigenvector of that character.
- A nontrivial order-two character with nonzero nondegenerate invariant
  mass, zero radical, and zero dual index. Self-dual data must not be
  reconstructed from that index.

The old `AuditWeylZeroModeSupport` additionally prints the compatibility
theorem's axioms and retains its existing concrete SU(6) regression cases.

```sh
lake build Physics.FieldTheory.Mass.Audit.AuditAbelianMassSpectrum \
  GUT.SU6.SelectionRules.Audit.AuditWeylZeroModeSupport
lake build
```

Verification at stage 01: targeted build 4195 jobs / 44 axiom-bearing
reports; full build 4397 jobs / 1463 reports. All scanned reports use only
`propext`, `Classical.choice`, and `Quot.sound`. No dependency pins changed.
