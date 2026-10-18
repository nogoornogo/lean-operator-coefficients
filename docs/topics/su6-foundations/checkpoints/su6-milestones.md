# completed su6 milestones

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

## Completed SU(6) Milestones

The entries below retain the progression of intermediate and stronger
endpoints. References to a previous NEXT STEP describe that historical
stage, not an outstanding task; later entries supply the stated extensions.

- Continuity-only embedding geometry, character rigidity, and the scoped
  charge-orbit-to-operator-neutrality Dirac/Yukawa
  assembly are checked. The final statement concerns an Abelian selection
  rule, without a nonzero decay-amplitude claim.
- Full compact-SU(6) Haar unitarization and the analytic `6`, `bar6`, and `15`
  with algebraic equivalences, dimensions, and weight certificates are checked.
  Construction details are in the representation-certificates dossier.
- `DiracWeylConvention.lean` constructs the invariant symmetric bilinear on
  `V + W*`, identifies its radical with the kernel plus dual cokernel, and
  proves the dual chiral-character conservation law via the existing signed
  mass index. Its persistent audit has the same standard axiom boundary.
- `ConcreteSU6Branching.lean` computes the actual characters and proves
  `15 + bar6 - 6 = 10 + bar5` on the standard torus (`coords 5 = 1`).
  `AuditConcreteSU6Branching.lean` checks the standard axiom boundary.
- `ConcreteSU6PhysicalTarget.lean` matches the actual signed source to the
  physical SM target at `(-2,3)`: one generation, no net singlets, and uniform
  charges in any additive Abelian group, including torsion.
- `ActualBlockChoiceIndependence.lean` proves that the selected semisimple embedding classification blocks do
  not change centralizer coefficients or circle exponents.
  `ConcreteStandardGeometry.geometry` has proved hypercharge pair `(-2,3)`.
- Previous NEXT STEP 1 is complete in `ConcreteDiracBenchmark.lean`:
  `model H` inhabits `ContinuousDiracYukawaModel H` for every Abelian `H`
  acting trivially, with generation index one and no spectrum hypothesis.
  `matter_resolvedCharacter` and `mass_hasExactSMChiralIndex` connect the
  actual source through the automatically chosen charge sectors to the
  canonical light index. The chosen mass/Yukawa sector is zero, proved by
  `model_massMap_eq_zero`. Extra vectorlike zero modes are not removed.
- Concrete construction exposed unresolved `rep` type names in
  `StandardBlockGaugeCancellation`: `autoImplicit` had made two source fields
  polymorphic and their summands uninhabited. Both fields now name the actual
  continuous-unitary representation type explicitly; all downstream proofs
  rebuild. See `MODEL_INTERFACE.md` for the audit correction.
- The new persistent audits check only `propext`, `Classical.choice`, and
  `Quot.sound`, plus actual constructors for trivial and finite Abelian groups.
- `InvariantWeylMass.lean` completes the previous NEXT STEP 1 foundation:
  invariant radical, nondegenerate invariant quotient, quotient self-duality,
  and dual chiral-character conservation, now generalized to arbitrary
  finite-dimensional complex group representations in milestone B.
  `dualIndex`/`lightDualIndex` package the unitary specialization in the existing
  finite virtual-character interface. The Dirac specialization recovers
  the antisymmetrized signed light index, not the original signed index.
- `WeylMassTwoTorsion.lean` gives a nontrivial one-dimensional sign action
  of a two-element group. Zero and nondegenerate Majorana masses have radical
  dimensions one and zero but identical dual indices. The persistent
  `AuditInvariantWeylMass.lean` checks constructors and standard axioms.
- `StandardWeylDualTarget.lean` completes the target part of NEXT STEP 1:
  dualization reverses both gauge weights and residual charges, commutes with
  Weyl permutations, and evaluates to the actual contragredient character.
  The fifteen SM weights are disjoint from their negatives, so the oriented
  charge profiles survive antisymmetrization. This yields standard charge-orbit bridge charge equalities
  and Abelian proton-operator neutrality neutrality from the radical's dual target. The actual charged-source
  specialization derives its character model and Weyl invariance, retaining
  an explicit UV field/source identification. `AuditStandardWeylDualTarget`
  checks standard axioms and two-torsion examples.
- `StandardWeylMassSource.lean` discharges `hSource` for canonical actual
  fields: nonnegative ordinary matter multiplicities survive full residual
  charge-sector decomposition, and finite orthogonal sums realize their
  character. `StandardWeylModel` contains no UV character-model field and
  proves Abelian proton-operator neutrality neutrality for arbitrary invariant symmetric masses, conditional
  on its explicit radical dual-SM target. Its hypercharge branch is fixed to
  the standard one. The audit checks one-copy dimension, zero-mass
  construction, finite-Abelian specialization, and standard axioms.
- `ConcreteWeylBenchmark.model H` constructs a full `StandardWeylModel H`
  from actual `15 + 2 bar6` matter with neutral action and zero mass, without
  assuming a spectrum certificate. The source differs from the old signed
  `15 + bar6 - 6` by the self-dual `6 + bar6`; the proved radical dual target
  is one generation for every invariant symmetric mass on this matter.
  The explicit model has field dimension and radical dimension 27. The
  singlet parameter zero is a dual-index statement, not absence of singlets.
  Its persistent audit constructs trivial- and finite-Abelian examples.
- `StandardWeylSupportedOperator.lean` provides a conditional UV result,
  not completion of NEXT STEP 1: it constructs the
  `SupportedInvariantOperator` witness for `StandardWeylModel`. The resolved UV
  character `pUV` from `ordinaryChargedSource M.matter` carries Weyl invariance
  and charge-profile equalities. Orbit compatibility `SU5OrbitCompatible M.charges`
  follows from `M.lightTarget`. With the `nonzeroOrbitProfiles` hypothesis
  (quark/down profiles nonzero at `M.charges`), `ChargesSupported` propagates
  to all five SM fields, and both `qque` and `duql` witness constructors fire.
  The selection-rule conclusions (`not_forbidsEverySupportedStandardOperator`,
  `not_forbidsEverySupportedPhysicalDeltaBOneOperator`, finite-Abelian variants)
  depend only on standard axioms.
- The reviewed `kilo` lemmas were merged with corrected scope in `checkpoint 01`.
  `AbelianActualSpectrum` now constructs nonnegative actual character
  multiplicities using the existing full-sector decomposition, proves their
  trace evaluation faithful, and extracts nonzero eigenvectors from support.
- `WeylZeroModeSupport` closes the oriented NEXT STEP 1 bridge when
  `0 < M.generations`: every SM weight/charge has a nonzero vector in the
  actual mass radical. Its `lightSpectrum` has nonnegative coefficients;
  the `qque`/`duql` witnesses need no `nonzeroOrbitProfiles` assumption.
  Negative generation indices force conjugate zero modes in a separate
  theorem. No full spectrum reconstruction or amplitude is asserted.
- `InvariantLineMass` proves that an invariant nonzero vector yields a
  complex-bilinear symmetric mass with a codimension-one radical.
  `ConcreteWeylNonzeroMass.model H` applies this to the original `15 + 2 bar6`
  canonical fields: mass nonzero, generation one, radical dimension 26.
  `not_all_symmetric_masses_zero` directly refutes the proposed impossibility
  in the actual model interface. This is not full vectorlike-mode lifting.
- `AuditWeylZeroModeSupport` constructs trivial- and finite-Abelian examples,
  including a nonzero-mass operator witness and all fifteen actual zero-mode
  sectors. All audited declarations use only the three standard axioms.
- `AbelianCharacterBasis` constructs an actual eigenbasis with prescribed
  character labels from trace equality, including repeated labels.
  `HyperbolicBasisMass` pairs opposite labels and identifies its radical's
  basis, dimension, and full character. `ConcreteWeylFullMass.model H`
  applies these to the original `15 + 2 bar6` fields: six pairs are lifted,
  leaving exactly one SM generation and no extra zero modes. The mass is
  nonzero and invariant under the declared physical torus times residual H.
  `AuditConcreteWeylFullMass` checks full spectrum, actual constructors, and
  standard axioms. No full non-Abelian gauge tensor or amplitude is asserted.

### Further Completed Endpoints

- `WeylConjugateOperator` packages negative-index support in an
   explicitly conjugated signature with inverted residual character and
   `threeB = -3`. For any nonzero index, a supported invariant operator or
   its conjugate exists. The two orientations are not identified. Its
   persistent audit includes finite-Abelian specialization and standard axioms.
- `ConcreteWeylFullMass` pairs the restricted `6` and `bar6`,
   including their singlets, and proves a 15-dimensional radical with the
   exact full SM character. The earlier rank-one/zero-mass benchmarks remain
   available as distinct examples. The
   [mass-support review](../../mass-profile-foundations/plans/MASS_SUPPORT_REVIEW.md) explains why the original
   impossibility argument used the wrong group.
- `PhysicalWeylMassSource` derives the physical dual target from
   canonical nonnegative matter and the actual mass radical at arbitrary
   cocharacters. `PhysicalWeylMomentBridge` and `PhysicalWeylChargeBridge`
   supply hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality from that same target. `PhysicalWeylZeroModeSupport`
   supplies actual radical support and both operator orientations.
   `ContinuousWeylModel` composes continuous semisimple embedding classification geometry with these results;
   `ContinuousWeylBenchmark` proves one-generation non-vacuity with zero mass.
   The permanent audit reports only the three standard axioms.
