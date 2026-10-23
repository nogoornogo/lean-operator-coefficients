# Standard branch and final assembly formalization

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. Scoped standard-branch
assemblies connect embedding, hypercharge, character/mass and
supported-signature interfaces.

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

The current positive-profile/scalar-family assembly is documented in
[finite charge profiles](finite-charge-profiles.md) and
[scalar-dependent models](scalar-dependent-model.md). It drops single-charge
and scalar-linear restrictions without adding orbit-equality or support
premises. The earlier signed/fixed-charge declarations below are retained
compatibility interfaces, not the limit of the current scope.

## 2. Inputs And Conclusion

Each source package retains its own exact target, mass invariance,
residual-action and geometry hypotheses; the catalogue includes older
compatibility routes.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Embedding and hypercharge bridges feed charge-orbit identities, actual support
and neutral supported operator signatures.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

- `GUT.CharacterExact`, `EquivariantMassIndex`, and
  `InvariantWeylMass.SymmetricMass.radical_dual_character_eq`
  - use TauCeti's exact-sequence trace theorem for kernel/cokernel character
    conservation over arbitrary fields and monoids, without semisimplicity;
  - identify the existing unitary orthogonal light index with the algebraic
    quotient-cokernel index, keeping the older theorem interfaces;
  - prove symmetric-mass dual-index conservation without inner-product or
    unitarity assumptions, using the self-dual massive quotient;
  - audit a nonsplit rational shear extension and retain the two-torsion
    zero-mode counterexample. See [the exact-character dossier](../../../inputs/Math/CHARACTER_EXACT.md).

- `Physics.WeylYukawaMass`, `ContinuousWeylYukawaModel`, and `WeylYukawaBenchmark`
  - derive symmetric masses from scalar-linear invariant Yukawa couplings,
    bare masses, and invariant VEVs, also after restricting to a vacuum
    stabilizer of an arbitrary (possibly non-Abelian) group;
  - realize the coupling as an actual tensor-product intertwiner;
  - compose the primitive-data model with the scoped assembly while retaining its IR dual target;
  - construct a nonzero full-SU(6) tensor on `6 + 6*` and a post-breaking
    nonzero-Yukawa 15-mode benchmark with zero bare mass;
  - `AuditWeylYukawa` checks standard axioms and that nonzero coupling alone
    does not force nonzero mass at zero VEV.

- `GUT.StandardWeylFieldIdentification`, `SymmetricMassTransport`,
  `ContinuousWeylMassTransport`, and `ContinuousWeylFullMass`
  - identify the actual canonical field bundles at the standard pair;
  - preserve the given mass and construct an equivalence of radical
    representations, also proving equality of the full actual spectra;
  - construct a nonzero-mass continuous-geometry model with the exact
    15-mode SM spectrum, audited by `AuditContinuousWeylFullMass`.

- `GUT.PhysicalWeylMassSource`, `PhysicalWeylZeroModeSupport`,
  `ContinuousWeylModel`, and `ContinuousWeylBenchmark`
  - derive the common physical dual target from canonical nonnegative actual
    matter and its symmetric mass radical at arbitrary cocharacters;
  - compose continuous semisimple embedding classification geometry, the odd-moment hypercharge character rigidity bridge, and standard charge-orbit bridge -> Abelian proton-operator neutrality;
  - derive actual zero-mode support and invariant operator signatures in
    either explicitly distinguished index orientation;
  - construct a one-generation zero-mass model with no spectrum premise;
  - `AuditContinuousWeylModel` checks finite-Abelian constructors and all
    endpoints with standard axioms. See the [scope dossier](../../../inputs/GUT/WEYL_MODEL.md).

- `GUT.AbelianCharacterBasis`, `HyperbolicBasisMass`, and `ConcreteWeylFullMass`
  - construct prescribed actual character eigenbases from faithful trace
    equality, respecting multiplicities;
  - pair opposite-character basis vectors by an invariant symmetric bilinear
    and prove the unpaired basis is exactly the radical;
  - on the canonical `15 + 2 bar6` fields, lift six pairs and prove a nonzero
    mass with radical dimension 15 and exact full SM character;
  - retain the declared physical-torus/residual-group invariance boundary;
  - `AuditConcreteWeylFullMass` checks standard axioms and premise-free
    constructors for trivial and finite Abelian residual groups.

- `GUT.AbelianActualSpectrum` and `WeylZeroModeSupport`
  - reuse full Abelian character sectors to construct nonnegative actual
    multiplicities, prove faithful evaluation, and extract nonzero vectors;
  - identify the actual radical's dual spectrum with the declared target;
    positive index yields all fifteen oriented SM sectors and supported
    `qque`/`duql` witnesses without a UV-support assumption;
  - prove conjugate-sector support separately for negative index;
  - `WeylConjugateOperator` packages that support in a separate conjugated
    signature with inverse residual character and signed baryon number -1;
    its audit checks the nonzero-index disjunction and both-orientation obstruction;
  - do not recover the full spectrum or change the general-hypercharge scoped theorem.
- `Physics.InvariantLineMass` and `ConcreteWeylNonzeroMass`
  - construct an invariant complex-bilinear symmetric rank-one mass using
    a nonzero invariant vector in the canonical `15 + 2 bar6` fields;
  - prove mass nonzero, generation one, and radical dimension 26;
  - refute the proposed uniqueness of zero mass under `CombinedGroup H`;
  - `AuditWeylZeroModeSupport` checks standard axioms and actual finite-Abelian
    constructors, including supported operators in the nonzero-mass model.
- `GUT.ConcreteWeylBenchmark`
  - constructs actual `15 + 2 bar6` ordinary matter with nonnegative
    multiplicities, proves neutrality of its automatically chosen charge
    sectors, and computes the canonical field character;
  - identifies its dual character with one neutral SM generation: the
    difference from the checked signed source is `6 + bar6`;
  - proves `mass_hasDualSMTarget` for every invariant symmetric mass on
    those fields and constructs `model H` with zero mass, without supplying
    a spectrum assumption. Field and radical dimensions are both 27;
  - `AuditConcreteWeylBenchmark` checks standard axioms and actual one-generation
    constructors for trivial and finite Abelian groups. This is not a
    full SM-only zero-mode spectrum or the general-hypercharge scoped extension.
- `GUT.StandardWeylMassSource`
  - constructs unitary all-left-handed fields by full charge-sector
    decomposition and finite orthogonal sums of nonnegative matter copies;
  - uses the new reusable `positive_character_of_nonnegative` theorem in
    `UnitaryVirtualRealization` to prove `ordinaryFields_character`, removing
    the generic mass endpoint's `hSource` assumption;
  - defines `StandardWeylModel` with no source-character field and proves
    Abelian proton-operator neutrality neutrality for an arbitrary invariant symmetric mass and an explicit
    radical dual-SM target, at the fixed standard hypercharge branch;
  - its persistent audit checks one-copy dimension, zero-mass construction,
    finite-Abelian specialization, and standard axioms. Its nonzero-generation
    witness is now checked above; the broader scoped assembly remains open.
- `GUT.StandardWeylDualTarget`
  - defines simultaneous gauge-weight/residual-charge dualization on the
    normalized `Finsupp` and proves compatibility with Weyl action and
    actual contragredient trace evaluation;
  - proves that all fifteen oriented SM weights avoid their negatives and
    retain their charge profiles in the dual difference; singlet coefficients
    become `s(q)-s(-q)` instead;
  - derives standard charge-orbit bridge charge equalities and Abelian proton-operator neutrality neutrality from a dual target, then
    connects the actual radical conservation theorem through faithful
    evaluation. The charged-source specialization derives its Laurent model
    and Weyl invariance but keeps the UV field/source identification explicit;
  - `AuditStandardWeylDualTarget` checks standard axioms and `ZMod 2`
    specializations. Full build passes in 4160 jobs. The model scope is unchanged.
- `Physics.InvariantWeylMass` and `WeylMassTwoTorsion`
  - construct the invariant radical of an arbitrary symmetric bilinear mass,
    the nondegenerate quotient form, and its equivariant self-duality;
  - prove dual chiral-character conservation for finite-dimensional unitary
    representations and expose `dualIndex`/`lightDualIndex` in the existing
    finite virtual-character interface;
  - recover the Dirac radical and its antisymmetrized signed index;
  - exhibit a nontrivial order-two action with identical dual indices but
    radical dimensions one and zero for zero and nondegenerate masses;
  - `AuditInvariantWeylMass.lean` checks actual constructors and only standard
    axioms. Its foundation milestone passed in 4158 jobs. The charge-resolved
    target bridge is now checked above; full model assembly remains open.
- `GUT.ConcreteDiracBenchmark`
  - constructs a neutral strict ordinary action for any Abelian group and
    proves neutrality of its automatically selected charge sectors;
  - proves the exact charge-resolved SM source character for `15 + bar6 - 6`
    and transports it to the canonical light index for any invariant mass;
  - constructs `model`, with generation index one and explicit zero mass,
    Yukawa family, and vacuum, and specializes the scoped theorem to it;
  - `exists_one_generation_model` closes non-vacuity without a supplied
    spectrum hypothesis. `model_massMap_eq_zero` records the limitation:
    vectorlike zero modes are not removed;
  - `AuditConcreteDiracBenchmark.lean` also checks actual common-gauge and
    finite-Abelian constructors, guarding against the repaired `autoImplicit`
    representation-field error documented in `MODEL_INTERFACE.md`.
- `GUT.ActualBlockChoiceIndependence` and `ConcreteStandardGeometry`
  - use Schur's lemma for unequal block dimensions to prove block-scalar
    naturality and independence of centralizer coefficients and circles from
    the chosen semisimple embedding classification decomposition;
  - construct continuous standard geometry with proved extracted pair
    `(-2,3)`, independently of the matter-spectrum assumption;
  - have persistent axiom audits; the full build passes in 4154 jobs with
    only standard axioms for the new audited declarations.
- `Physics.DiracWeylConvention`
  - constructs the symmetric bilinear on `V x W*` from a Dirac intertwiner,
    proves full-group invariance, and identifies its invariant radical;
  - identifies annihilator representations with the dual of an invariant
    complement using the canonical dual of a quotient;
  - proves `radical_character_eq_kernel_add_dual_cokernel`, then relates the
    radical's dual chiral difference to the antisymmetrized signed light
    index and the ultraviolet all-left-handed dual chiral difference;
  - is audited by `AuditDiracWeylConvention.lean` with only standard axioms.
    The general bilinear foundation is now checked separately above. Its scoped
    adapter and a full SM-only zero-mode spectrum remain separate obligations;
    the index-based benchmark is now checked.
- `GUT.StandardSU5Orbit`
  - defines the normalized `Fin 5` Laurent exponent model and its `S_5` Weyl
    action;
  - proves, at every invariant residual shift, equality of the three `10`
    representative coefficients and equality of the two anti-fundamental
    representative coefficients in every Weyl-invariant polynomial.
- `GUT.StandardBranchProtonObstruction`
  - proves in every additive commutative charge group that explicit `SU(5)`
    orbit charge equalities neutralize both gauge-mediated proton-decay
    functionals;
  - proves the two mixed-anomaly identities for one rational charge assignment
    and their anomaly-free consequence, without assuming family-by-family
    vanishing from globally cancelled family-dependent anomalies.
- `GUT.StandardU5Group`
  - constructs the injective standard block homomorphism
    `U(5) -> SU(6), A |-> diag(A, det(A)^-1)`;
  - proves that every determinant-one diagonal `SU(6)` point lifts through
    this subgroup and identifies actual and finite virtual restricted trace
    characters on the lifted torus;
  - composes those identities with supplied ambient Laurent models.
- `GUT.StandardAbelianCharge`
  - defines the canonical rank-four `SU(5)` weight normal form together with
    an arbitrary additive Abelian residual-charge label;
  - pushes integer central degrees through `Integer ->+ A`, summing collisions
    in finite charge groups, and proves the resulting character remains
    `S_5`-invariant;
  - proves equality of the complete charge profiles of `Q,u^c,e^c` and of
    `d^c,L`, with explicit finite-Abelian and `ZMod N` conclusions;
  - composes standard charge-orbit bridge with Abelian proton-operator neutrality for exact pure-SM profiles and for occupied
    family-dependent charge sectors, without using anomaly cancellation.
- `GUT.StandardPhysicalSource`
  - models the residual charge of each weight as an independent ultraviolet
    source offset plus the image of its central `U(5)` degree;
  - constructs charge-resolved characters from finite virtual collections of
    actual jointly continuous unitary `SU(6)` representations and proves
    chargewise `S_5` invariance, retaining finite-charge collisions;
  - derives the standard charge-orbit bridge-to-Abelian proton-operator neutrality proton-functional conclusions for exact pure-SM and
    family-dependent occupied spectra in arbitrary additive Abelian, finite
    Abelian, and finite cyclic charge groups, without invoking continuous U(1) anomaly cross-check.
- `GUT.FiniteAbelianChargeSectors`
  - distinguishes an Abelian residual group `H` from its additive group
    of physical circle-valued characters;
  - decomposes every finite-dimensional unitary `H` action commuting with an actual jointly
    continuous unitary `SU(6)` representation into independent, spanning full
    character eigenspaces which remain actual `SU(6)` subrepresentations,
    without requiring `H` itself to be finite;
  - proves the sector direct sum is representation-equivalent to the original
    source and has the same trace character, then constructs the corresponding
    affine charged source and pointwise residual-group proton phases, retaining
    explicit finite-Abelian specializations.
- `GUT.StandardCentralGauge`
  - constructs the continuous standard central circle
    `z |-> diag(z,z,z,z,z,z^-5)` inside the checked `U(5) -> SU(6)` embedding;
  - proves that Laurent evaluation on this circle is exactly
    `z^totalDegree`.
- `GUT.FiniteResidualActionFactorization`
  - factors a supplied gauge-twisted Abelian physical action into its inner
    gauge lift and a unitary action commuting with all of `SU(6)`;
  - constructs the canonical identity gauge lift for a strict ordinary
    Abelian action commuting with the full `SU(6)` action and proves that the
    gauge-removed action is the originally supplied action;
  - derives continuity of the external action and its charge characters from
    continuous physical data, with unique integer sector charges for a
    residual circle;
  - proves on the actual hypercharge character rigidity Laurent weight basis that physical phases equal
    the affine `offset + centralDegree` charges used by standard charge-orbit bridge;
  - packages arbitrary, continuous, and finite Abelian exact pure-SM sources
    and derives trivial proton-operator characters through standard charge-orbit bridge followed by Abelian proton-operator neutrality,
    without an anomaly premise.
- `GUT.StandardSMCharacterTarget`
  - embeds normalized `SU(5)` weights injectively into the standard physical
    compact four-torus and combines them with arbitrary residual-group
    characters;
  - proves the resulting evaluator faithful by Dedekind linear independence,
    including for finite Abelian residual groups;
  - realizes the exact fifteen-weight SM character plus arbitrary
    charge-resolved gauge singlets as an actual finite virtual representation;
  - derives the exact standard charge-orbit bridge charge profiles, orbit equalities, and trivial
    proton-operator characters from whole-character equivalence, with explicit
    finite-Abelian and standard-central specializations and no continuous U(1) anomaly cross-check premise.
- `GUT.StandardPhysicalCharacterBridge`
  - splits every ambient weight at the standard pair `(-2,3)` into its
    normalized physical-torus exponent and standard-central degree;
  - constructs an actual product-group representation on each charged source
    sector and proves that its trace is exactly the faithful charge-resolved
    Laurent evaluation;
  - assembles these sectors into the finite virtual source character and proves
    that the reconstructed residual action agrees, sector by sector, with the
    supplied gauge-twisted physical action;
  - removes the separate source-side `IsCharacterModel` hypothesis and derives
    the exact standard charge-orbit bridge profile and Abelian proton-operator neutrality proton-character conclusion for arbitrary,
    continuous, and finite Abelian residual groups from actual target-character
    equivalence, without using continuous U(1) anomaly cross-check.
- `GUT.StandardPhysicalSpectrumBridge`
  - states the exact SM chiral-index profile by local coefficients: the
    fifteen non-singlet SM weights have the stated generation index, weight
    zero carries an arbitrary finite singlet index, and every other nonzero
    gauge weight has zero chiral index;
  - proves these local conditions equivalent to equality with the canonical
    charge-resolved `Finsupp`, including injectivity and nonvanishing of the
    fifteen explicit SM weights;
  - derives the actual whole product-group character equivalence from those
    conditions and the checked source trace calculation;
  - packages arbitrary, continuous, and finite Abelian physical sources with
    no separate character-model or character-equivalence field and proves the
    standard charge-orbit bridge charge equalities and Abelian proton-operator neutrality proton-character conclusion without continuous U(1) anomaly cross-check.
- `GUT.StandardBlockGaugeCancellation`
  - proves in an arbitrary additive Abelian charge group that the color- and
    weak-block contributions of a centralizer-valued gauge representative
    cancel from both proton charge functionals;
  - extracts those two block characters from the checked actual compact
    centralizer without decomposing them into the index-five `Y5/X` lattice or
    assuming roots of finite-group characters;
  - constructs the full external-character source from finite collections of
    actual gauge-twisted continuous-unitary `SU(6)` summands sharing one gauge
    lift, and proves that restoring the lift recovers each physical action;
  - converts finite virtual sources with strict commuting ordinary Abelian
    actions canonically to this interface using the identity lift;
  - combines the coefficient-level SM chiral-index profile, standard charge-orbit bridge Weyl-orbit equality,
    and Abelian proton-operator neutrality cancellation into trivial physical proton characters for arbitrary
    and finite Abelian residual groups, under explicit gauge-lift,
    centralizer, and low-energy charge-identification certificates.
- `GUT.StandardBlockChargeProjection`
  - retains raw ambient weights until the independent color/weak block
    characters have been evaluated, so no fifth roots of finite residual
    characters are assumed;
  - proves the family-dependent profile form of standard charge-orbit bridge to Abelian proton-operator neutrality: occupied physical
    `Q` and `d^c` profiles produce charges supported by all five SM profiles
    on which both proton functionals vanish, for every additive Abelian charge
    group;
  - applies this theorem to the actual common-gauge source and separately to
    finite Abelian residual groups, with all charge collisions summed;
  - constructs the resolved character directly from strict ordinary Abelian
    actions, proves the identity lift has zero color/weak charge, and derives
    the direct physical equalities `k_Q = k_u = k_e` and `k_d = k_L` together
    with both proton-character conclusions for arbitrary and finite Abelian
    groups.
- `GUT.StandardBlockPhysicalCharacterBridge` and
  `GUT.ActualBlockConjugacy`
  - identify the block-resolved evaluator with the trace of the supplied
    physical action after constructing one actual `SU(6)` standardizing
    conjugator for the complete compact centralizer;
  - identify the ordinary resolved character with the finite virtual trace of
    the originally supplied strict commuting actions, and identify an exact
    ordinary source trace with the canonical SM-plus-singlets target.
- `GUT.StandardAbelianProtection`
  - uses the concrete standard local-operator classes below as its primary
    selection-rule interpretation;
  - proves that an ordinary Abelian charge rule cannot charge both proton
    operator classes for every field-charge assignment supported by the
    physical chiral profiles, including the finite Abelian case;
  - states the occupancy-source, exact-spectrum, and present-channel
    conclusions directly for strict ordinary Abelian sources, without a gauge
    lift or a continuous-anomaly premise;
  - constructs a positive supported invariant-operator witness and does not
    infer a nonzero Wilson coefficient or amplitude.
- `Physics.StandardModelLocalOperator`
  - defines the physical `qque` and `duql` four-fermion signatures and checks
    their integral gauge, Lorentz, hypercharge, dimension, baryon-number, and
    lepton-number data;
  - supplies explicit color, weak, and left/right spinor epsilon slot plans,
    and proves the determinant tensors invariant and nonzero;
  - proves that the physical residual characters of these operator classes
    are exactly the two Abelian proton-operator neutrality proton characters;
  - packages a supported neutral class as `SupportedInvariantOperator`, giving
    the standard selection-rule obstruction without a channel-nonzero premise;
  - distinguishes the legacy two-class predicate from the literal universal
    predicate over every signature satisfying `IsPhysicalDeltaBOneOperator`,
    classifies every such signature by field multiplicities, and proves the two
    protection predicates equivalent;
  - proves that one supported canonical witness refutes the universal
    predicate.
- `GUT.AuditStandardChargeOrbitBridge`
  - permanently audits the concrete standard subgroup, trace restriction,
    affine charge projection, finite-charge collision handling, physical
    continuous-unitary sources, unitary Abelian character-sector decomposition,
    gauge-twisted action factorization and its continuous specialization,
    faithful charge-resolved target evaluation, profile equalities, and the
    anomaly-independent standard charge-orbit bridge-to-Abelian proton-operator neutrality compositions.
- `GUT.AuditHyperchargeStandard`
  - permanently audits the primitive-lattice classification, the
    color-neutral countercase and exclusion, the degree-five symmetric
    invariant and finite-weight-moment classification, the generic signed
    Weyl representative, the concrete physical SM target, the normalized
    standard-branch Weyl-orbit coefficient equalities, and the proton
    functional and anomaly identities.
- `GUT.SmoothEmbeddingBridge`,
  `GUT.ContinuousEmbeddingRegularityBridge`, and
  `GUT.StandardSmoothEmbeddingWitness`
  - turn Frechet differentiability of the actual matrix embedding in source
    exponential coordinates into the complete semisimple embedding classification one-parameter differential;
  - derive skew-adjointness and trace zero by differentiating the defining
    `SU(6)` equations, rather than taking target tangent membership as input;
  - provide an ambient matrix-extension interface and instantiate it for the
    concrete standard block embedding;
  - use continuous one-parameter subgroup classification and the Trotter
    formula to derive the linear compact-real differential from continuity
    alone, then prove the full exponential-coordinate map Frechet
    differentiable at zero.
- `GUT.FinalNoGoAssembly` and `GUT.AuditScopedNoGoAssembly`
  - construct the semisimple embedding classification `3+2+1` data from a continuous actual embedding,
    corestrict the actual hypercharge circle to its physical centralizer, and
    extract and reconstruct its unique primitive integer cocharacter;
  - check the flipped route from oriented branch data through the flipped
    obstruction and then standard charge-orbit bridge to Abelian proton-operator neutrality;
  - independently check a hypercharge character rigidity route in which the actual physical-torus
    character fixes the standard pair before the conditional standard
    charge-resolved spectrum enters standard charge-orbit bridge and Abelian proton-operator neutrality;
  - additionally check the stronger single-spectrum route described below,
    with arbitrary and finite Abelian endpoints;
  - expose a positive supported invariant local-operator witness along every
    route, with present-channel theorems retained only as conditional
    corollaries;
  - expose `MatrixDifferentiableInvariantMassPairingSource`, where invariance
    of a Hermitian mass pairing proves the required equivariant mass map, and
    derive the universal physical-operator selection-rule refutation directly,
    including for finite Abelian groups;
  - expose `ContinuousInvariantMassPairingSource`, which derives the legacy
    differentiability field automatically and carries the same hypercharge character rigidity-to-standard charge-orbit bridge-to-Abelian proton-operator neutrality
    conclusions with no differentiability premise, including for finite
    Abelian groups.
- `GUT.EquivariantMassIndex`
  - proves that an invariant Hermitian mass pairing induces an intertwiner when
    the target representation is unitary;
  - constructs the invariant pairing from an intertwiner and proves the
    resulting round trip, before applying the existing kernel/range index
    theorem.
- `GUT.PhysicalChargeResolvedBridge` and
  `GUT.AuditPhysicalChargeResolvedBridge`
  - construct one canonical finite character on
    `PhysicalExponent x ChargeLabel` from the full character eigensectors of
    an actual strict ordinary Abelian source at any integral cocharacter pair;
  - prove that forgetting residual charges recovers the actual hypercharge character rigidity Laurent
    restriction, including all finite-charge collisions;
  - prove that at `(-2,3)` the same character is the injective image of the standard charge-orbit bridge
    normalized character;
  - turn one local exact-SM coefficient certificate into both the hypercharge character rigidity pair
    classification and the standard charge-orbit bridge coefficient spectrum used by Abelian proton-operator neutrality.
- `Physics.DiracYukawaMass`
  - defines invariant bare Dirac masses, equivariant scalar-dependent Yukawa
    maps, and invariant vacuum expectation values for finite-dimensional
    representations of the unbroken group;
  - proves that evaluating the Yukawa family at the vacuum and adding the bare
    mass produces an intertwiner;
  - converts that intertwiner to the existing invariant Hermitian mass-pairing
    interface and proves the map-level round trip;
  - provides a zero sector and a compatibility constructor from any existing
    invariant bare mass, without claiming a general Weyl/Majorana semantics.
- `GUT.DiracPhysicalModel` and `GUT.AuditDiracPhysicalModel`
  - define the scoped post-SU(6), pre-electroweak
    `ContinuousDiracYukawaModel` over the physical torus and an arbitrary
    ordinary Abelian residual group;
  - retain the exact charge-resolved Standard Model chiral index as an explicit
    applicability field and derive the mass map and earlier continuous
    invariant-pairing source from primitive Dirac data;
  - prove the complete `semisimple embedding classification -> hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality` supported-operator
    selection-rule obstruction, with a direct finite-Abelian specialization;
  - lift every older invariant-pairing source compatibly and prove preservation
    of its mass map;
  - audit all exposed bridge and endpoint declarations with dependencies only
    on `propext`, `Classical.choice`, and `Quot.sound`.

- `Physics.SMEpsilonTensor`, `Physics.StandardSMGaugeTensor`,
  `GUT.StandardSMResidualTensor`, and `Physics.AuditStandardSMGaugeTensor`
  - realize the color/weak determinants as tensor-product linear maps;
  - construct ordered `qque` and `duql` tensors on standard field spaces,
    prove full covering-gauge invariance, and exhibit values equal to one;
  - recover the exact Abelian proton-operator neutrality residual characters from fieldwise actions and
    prove invariance iff those characters are trivial, for any Abelian group;
  - apply standard charge-orbit bridge -> Abelian proton-operator neutrality to these tensors, with finite-group positive and negative
    audits; actual-radical identification and Grassmann semantics remain open.

- `GUT.SplitWeylMass`, `GUT.SplitRepresentationProjection`,
  `GUT.StandardSMFullGaugeMass`, `GUT.StandardSMRadicalTensor`,
  and `GUT.AuditStandardSMRadicalTensor`
  - construct a full-gauge-invariant nonzero symmetric mass on a decomposed
    27-dimensional field representation and prove its radical is the
    15-dimensional all-left-handed SM representation;
  - transport the nonzero ordered tensors to the radical and its dual using
    explicit equivariant retractions and bidual maps;
  - preserve Abelian proton-operator neutrality residual transformation laws and audit finite-group
    compatible/incompatible examples; canonical SU(6) branching remains open.

- `GUT.StandardSMGroup`, `GUT.StandardSMTorus`,
  `GUT.StandardSMContragredient`, and `GUT.AuditStandardSMBranching`
  - construct the continuous standard covering-group homomorphism into
    SU(6) and prove exact agreement with the physical torus at `(-2,3)`;
  - identify the analytic `6` with the mass benchmark's heavy representation
    and the analytic `bar6` with its dual, including the epsilon-based
    lepton identification and neutral residual compatibility;
  - audit an off-diagonal weak rotation and a nonidentity kernel element;
    the following milestone supplies the exterior square and UV direct product.

- `GUT.StandardSMExterior`, `GUT.StandardSMUVFields`,
  `Physics.EquivariantWeylMassTransport`, `GUT.StandardSMUVMass`,
  and `GUT.AuditStandardSMUVMass`
  - construct exterior branching by an alternating map and prove its
    surjectivity, bijectivity, and full-group intertwining;
  - assemble the actual analytic SU(6) `15 + 2 bar6` direct product, prove
    joint continuity, and identify its restriction with the neutral mass
    benchmark, including exact physical-torus compatibility;
  - pull back the nonzero symmetric mass and prove the full 15-dimensional
    SM radical equivalence and nonzero invariant ordered tensors;
  - audit exterior signs and a zero-mass/27-mode negative control, with only
    standard axioms; the next milestone supplies a compatible carrier adapter.

- `GUT.AbelianCharacterEquivalence`, `GUT.ContinuousRepresentationTransport`,
  `GUT.RepresentationConjugation`,
  `GUT.StandardSMOrdinaryFields`, `GUT.StandardSMOrdinaryMass`,
  `GUT.StandardSMContinuousTensor`, and `GUT.AuditStandardSMOrdinaryModel`
  - construct an actual torus/residual equivalence from the proved unitary
    character equality and a compatible continuous SU(6) extension on the
    canonical fields, with exact restriction equalities;
  - transport the full-gauge mass and actual SM radical into the continuous
    model, retaining nonzero mass and the complete charge-resolved spectrum;
  - construct nonzero invariant ordered tensors on that model's radical,
    with witnesses equal to one and a zero-mass/27-mode negative control;
  - this is a neutral-residual existence construction, not an identification
    of an independently specified natural full action or the older mass.

- `Physics.SymmetricScalarYukawa`, `Physics.ContinuousSymmetricScalar`,
  `GUT.UnitarySymmetricScalar`, `GUT.StandardSMUVYukawa`,
  and `GUT.AuditStandardSMUVYukawa`
  - construct symmetric bilinear-form scalars and the full-group-invariant
    evaluation Yukawa family independently of a chosen mass;
  - prove scalar joint continuity in finite dimensions and apply Haar
    unitarization for an actual continuous unitary SU(6) scalar model;
  - recover any invariant restricted symmetric mass by a constructed VEV
    with zero bare mass, and identify the VEV stabilizer with the form's
    preserving elements, not with a prescribed unbroken subgroup;
  - specialize to the full-gauge 15-mode benchmark, retaining exact mass
    equality and canonical-carrier coefficient pullback;
  - audit full SU(6) invariance, finite-Abelian neutral actions, and the
    same nonzero coupling at zero VEV leaving 27 modes; no vacuum dynamics,
    minimal Higgs content, or amplitude is asserted.

- `GUT.StandardSMUVCoordinates`, `GUT.StandardSMUVStabilizer`,
  and `GUT.AuditStandardSMUVStabilizer`
  - expose the existing branching equivalences and mass in algebraic coordinates;
  - prove that the signed exchange of color coordinate 0 and weak coordinate 3
    preserves that mass and its actual continuous unitary scalar VEV;
  - exclude this SU(6) element from the SM image by its nonzero off-block entry;
  - prove strict SM containment in the VEV stabilizer, retaining the nonzero
    15-mode benchmark; no full stabilizer classification or vacuum dynamics.

The first Lean milestone avoids using integral-domain cancellation: it proves
the non-invariance of the full product directly by canonical Laurent-polynomial
computation. The closed polynomial equalities and inequalities are discharged
with `decide`.

## 6. Scope And Limitations

Ordered tensors, neutral signatures, Grassmann operators, Wilson coefficients
and amplitudes are distinct endpoints. Older pending notes describe their
checkpoint, not the present project queue.

## 7. Sources And Verification

The [scope dossier](../SCOPED_NO_GO_THEOREM.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.
