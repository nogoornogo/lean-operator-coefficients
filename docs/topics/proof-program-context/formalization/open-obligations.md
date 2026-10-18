# Open and informal formalization obligations

Archived at stage 01. This is a historical checkpoint, not a maintained
list of current obligations. Some extensions described as open below were
subsequently completed. Consult the [current assumptions](../../../proof/ASSUMPTIONS.md)
and [topic records](../../README.md) before treating any item as open.

### Standard-chain extension

The [standard SU(5) chain roadmap](../../standard-chain-foundations/plans/STANDARD_SU5_CHAIN_PLAN.md) is
complete in its declared scope. Its shared mass/support core, actual SU(5)
source, ambient composition, legacy adapters, and
[standard SU(N) family](../../../proof/current/applications/GUT/interfaces/standard-su-n.md) are checked. The chosen standard
chain and exact positive dual light target remain explicit hypotheses, not
unfinished source lemmas. Arbitrary embeddings, vacuum dynamics, and nonzero
amplitudes are not conclusions of this extension. The optional items below
are not an active queue; see [Topic records](../../README.md).

### Standard mathematics still to specialize/prove

- if the conclusion is stated using the conventional Grothendieck
  representation ring `R(G)`, connect that construction to the now-checked
  virtual-character quotient.  The latter quotient and its restriction map are
  already defined; the independent compact-group character-classification
  theorem is what remains.
- extend the concrete Weyl-representative construction from this generator to
  the full relative Weyl action if the final proof needs all of S4 rather than
  just the obstructing `(3 6)` generator;
- prove that the required global `SU6TorusEigenbasisTheory` exists for the
  whole intended class of actual SU(6) representations. For physics
  representations this should be a continuous/smooth/algebraic
  finite-dimensional representation theorem; arbitrary abstract group
  representations are too broad for torus Laurent polynomiality.  The current
  Lean-certified substitute is the constructive tensor/exterior-generated
  subquotient class in
  `GUT.CertifiedConstructions.TensorGeneratedSubquotientSU6Representation`.
  This is no longer required for the `(3 6)` no-uplift contradiction itself:
  the function-level audit theorem excludes arbitrary finite virtual restricted
  characters without assigning Laurent polynomials to the source summands.
- the normalized 30-term flipped SM character is now kernel-checked against
  the image of both the older list/factored model and its explicit expansion.


### Currently informal / unverified

- identification of the checked virtual-character quotient with a conventional
  compact-group Grothendieck representation ring, if literal `R(G_SM)` notation
  is retained;
- full Lie-theoretic construction covering every intended
  continuous/smooth/algebraic finite-dimensional SU(6) representation, by
  connecting it to the currently certified tensor/exterior-generated
  subquotient certificate class (an independent Laurent-realization result,
  no longer a dependency of the `(3 6)` function-level no-uplift theorem);
- the hypercharge character rigidity finite-weight source bridge is closed for finite-dimensional jointly
  continuous complex `SU(6)` representations: Haar averaging constructs the
  unitary model used by the torus decomposition.  The checked Dirac-type
  physical model records equality with the explicit SM-plus-singlets chiral
  target as `HasExactSMChiralIndex`; deriving that condition for a concrete
  model is an applicability proof, not a theorem about every Lagrangian.  From
  that equality onward, faithful recovery of the exact finite-weight
  character, the fifth moment, and `(m,n)=(-2,3)` are Lean-checked, including
  finite weight collisions and arbitrary gauge singlets;
- alternatively, the older standard/flipped branch route still lacks the
  implication from the exact SM-only virtual representation-ring hypothesis
  to an oriented neutral defining block and its conjugacy/orientation
  transport; primitive lattice arithmetic and the actual color-neutral
  exclusion are checked;
- optional abstract smooth-manifold/Lie-group packaging of the checked
  ambient-matrix derivative as a tangent-bundle equivalence for the physical
  centralizer subgroup; the concrete derivative and its `Y5/X` coordinates
  are already Lean-checked;
- optionally strengthen the now-checked concrete Dirac benchmark to a
  nonzero mass sector that lifts unwanted vectorlike modes and identifies the
  full light spectrum. `ConcreteDiracBenchmark.model` already supplies every
  field of `ContinuousDiracYukawaModel` with standard continuous geometry,
  actual `15 + bar6 - 6` matter, neutral residual action, generation index one,
  and zero mass/Yukawa data. Its exact canonical light chiral index is proved.
  Non-vacuity of the index-based model class is therefore closed; the full
  SM-only zero-mode spectrum is not established by this witness;
- checked symmetric linearized extension, with further semantics still
  optional: `InvariantWeylMass`
  now proves invariance of the radical, equivariant self-duality of the
  nondegenerate quotient, and `[F] - [F*] = [rad b] - [(rad b)*]` at the
  finite virtual-character level for unitary actions. Its Dirac specialization
  is the antisymmetrization of the existing signed index. `StandardWeylDualTarget`
  now supplies the charge-resolved target convention, recovery of the oriented
  SM profiles used by standard charge-orbit bridge, and the conditional actual-mass connection to Abelian proton-operator neutrality.
  `StandardWeylMassSource` now discharges `hSource` for canonical fields from
  nonnegative ordinary matter and gives `StandardWeylModel.proton_functionals_eq_zero`
  at the fixed standard branch. `ConcreteWeylBenchmark` now constructs a
  one-generation witness with actual `15 + 2 bar6` matter, neutral action,
  and zero mass; its radical has dimension 27. `WeylZeroModeSupport` now
  derives actual radical support and the operator-signature endpoint for
  positive generation index; negative index gives conjugate zero modes.
  `ConcreteWeylNonzeroMass` supplies a nonzero rank-one mass on the same
  matter, leaving 26 modes. `ConcreteWeylFullMass` now lifts all twelve extra
  modes and proves the full 15-dimensional SM radical, under the declared
  torus/residual-group invariance. `PhysicalWeylMassSource` and
  `ContinuousWeylModel` now completes the general-hypercharge embedding/character-rigidity/scoped assembly
  using that dual convention. The scalar-linear symmetric Yukawa/VEV
  bridge is now checked in `WeylYukawaMass` and `ContinuousWeylYukawaModel`,
  with actual invariant mass/Yukawa tensors for arbitrary groups. The
  [scalar-family extension](../../../proof/current/applications/GUT/SCALAR_DEPENDENT_MODEL.md) now also
  removes scalar-linearity; the [profile endpoint](../../../proof/current/applications/GUT/PROFILE_MODEL.md)
  handles positive family-dependent targets, derives their orbit equalities,
  and composes both extensions. Its SU(5) adapter and actual two-charge
  SU(6) example are checked, not open source obligations. Remaining
  extensions are general Lagrangian semantics and full non-Abelian proton
  operator tensors on the actual radical. The latter first needs a full
  unbroken gauge action and mass invariance, beyond torus invariance alone.
  The ordered tensors on standard field spaces are now constructed in
  `StandardSMGaugeTensor`; `StandardSMResidualTensor` recovers Abelian proton-operator neutrality on the
  actual tensor-product action. This does not supply the radical embedding
  or nonvanishing after the fermionic quotient. See
  [the tensor scope](../../../proof/current/applications/Physics/SM_GAUGE_TENSOR.md).
  `StandardSMFullGaugeMass` and `StandardSMRadicalTensor` now close this
  radical/tensor construction for a decomposed 27-dimensional post-breaking
  candidate. `StandardSMExterior`, `StandardSMUVFields`, and `StandardSMUVMass`
  now prove its full-gauge lift to actual analytic SU(6) `15 + 2 bar6`, with
  neutral residual action, nonzero mass, exact SM radical, and both tensors.
  `StandardSMOrdinaryFields` now constructs a torus/residual equivalence
  and compatible continuous SU(6) extension on `ordinaryFields`.
  `StandardSMOrdinaryMass` and `StandardSMContinuousTensor` carry the mass,
  exact SM spectrum, and nonzero invariant tensors into the continuous
  model. An independently specified natural charge-sector full action is
  not identified with this extension. `StandardSMUVYukawa` now gives a
  continuous-unitary full-SU(6) scalar/Yukawa realization of this mass with
  zero bare mass and a constructed SM-fixed VEV. This universal nonminimal
  existence construction does not prescribe Higgs content, supply a scalar
  potential, or give an exact-SM vacuum. `StandardSMUVStabilizer` now proves
  the existing VEV's stabilizer strictly larger than SM. Equality for this
  unchanged VEV is refuted, not pending; an exact-SM construction requires
  different or additional scalar data and a new proof. That extension,
  natural-action identification, and Lorentz/Grassmann nonvanishing
  remain optional extensions; see
  [the mass scope](../../../proof/current/applications/GUT/SM_GAUGE_MASS.md).
  `ContinuousWeylMassTransport` now preserves the actual mass and radical,
  and `ContinuousWeylFullMass` closes the nonzero 15-mode benchmark transport.
  `WeylConjugateOperator` now closes the separate negative-
  index endpoint with explicit conjugate support and inverse character.
  `WeylMassTwoTorsion` proves that the dual difference loses self-dual data:
  identical dual indices can have different radical dimensions under a
  nontrivial order-two action. Majorana singlets and self-dual gauge sectors
  must not be discarded implicitly;
- optional stronger extension: the physical flavor/Yukawa interpretation
  needed to turn the checked
  family-dependent supported-sector conclusion into a statement about
  required nonzero gauge amplitudes.  This is separate from the already
  checked ordinary-Abelian selection-rule calculation and from continuous U(1) anomaly cross-check;
- upgrade of the checked semisimple embedding classification branch-count conclusion to the exact
  conjugacy/source-automorphism classification of embeddings;
- the finite-dimensional post-SU(6)-breaking, pre-electroweak Dirac-type model
  class and its adapter now give a checked strict ordinary-Abelian
  selection-rule theorem.  The exact charge-resolved SM chiral index remains
  an applicability hypothesis, and a nonzero channel remains an explicit
  premise only for an optional stronger corollary. The separate symmetric
  linearized model has its own checked dual-index endpoint, not a general
  Lagrangian theorem. continuous U(1) anomaly cross-check remains only an auxiliary continuous-`U(1)`
  cross-check, while the flipped route remains a separate representation-theoretic
  obstruction.
