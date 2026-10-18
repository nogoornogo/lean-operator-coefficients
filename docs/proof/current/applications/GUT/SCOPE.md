# Scope boundary and unresolved cases

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Current included scope

The intended scoped theorem concerns a finite-dimensional mass sector after SU(6)
breaking and before electroweak breaking.  Its candidate protecting symmetry
is a unitary Abelian action commuting exactly with the full ultraviolet SU(6)
action.  Its infrared condition is equality of the exact massless **chiral
index**, not equality of the complete zero-mode spectrum; additional
vectorlike zero-mode pairs are not excluded by that condition.

Two finite-dimensional mass conventions are checked separately: a signed
Dirac kernel/cokernel index and the dual radical index of a symmetric
all-left-handed linearized bilinear. The latter has a continuous-geometry
endpoint in [WEYL_MODEL.md](../../inputs/GUT/WEYL_MODEL.md). Neither convention reconstructs
the full light spectrum from its index.

The [profile endpoint](PROFILE_MODEL.md) now allows finite nonnegative
family-dependent charge distributions with a common positive total in the
symmetric-mass convention. Their equalities are derived from the actual
source. Its scalar-family wrapper also accepts the checked continuous
nonlinear mass sources; fermion dependence remains bilinear.
The common count may be any positive natural number, not just three.
The residual `H` need not be finite or topological in this interface;
`CommGroup H` and its strict unitary action remain required. Realistic masses
and CKM mixing are neither assumed nor derived. The
[relaxation table](../../../../topics/proof-program-context/assumption-checkpoint.md#conditions-no-longer-required) distinguishes
these facts from the separate signed-index and retained SU(5) results.

The physical-model terminology and assumption/derivation boundary are fixed in
[MODEL_INTERFACE.md](MODEL_INTERFACE.md).

## 4. Proof structure

### Standard Chain And SU(5)

The [standard-chain core](../../../../topics/standard-chain-foundations/plans/STANDARD_SU5_CHAIN_PLAN.md) additionally handles
arbitrary finite-dimensional unitary SU(5) matter, conditional on the exact
positive-profile dual radical target and strict commuting Abelian action.
It derives Weyl/profile equalities and supported neutral torus-mode
signatures. This does not promote those modes to full-SM radical tensors;
the retained-matter result below has that stronger, separate conclusion.
The ambient pullback is checked for a supplied SU(5) -> G homomorphism;
its continuous wrapper requires a continuous injective inclusion and joint
product-action continuity. The [standard SU(N) family](interfaces/standard-su-n.md)
constructs that inclusion for every N >= 5 and retains the exact dual
target as an input. It does not classify arbitrary SM embeddings or derive
vacuum dynamics. The actual SU(7) benchmark retains extra vectorlike and
singlet zero modes, consistently with that index-only condition.

The [SU(5) endpoint](SU5_SELECTION_RULE.md) is checked for retained actual
`n(10 + bar5)` with `n > 0` and a commuting unitary Abelian action. It permits
independent charge choices at each signature slot and refutes universal
charge prohibition using actual supported neutral signatures. Both nonzero
ordered internal tensors descend to the exact SM central quotient. It has
an explicit one-generation inhabitant and no assumed charge-equality bridge.

Unlike the SU(6) index models, this first SU(5) class assumes the actual
retained matter content. It does not derive it by integrating out arbitrary
heavy matter. It proves neither a nonzero amplitude nor nonvanishing after
the Lorentz/Grassmann quotient, and is not a theorem for all SU(5) models.

### Compact Symplectic Chirality

The separate [USp(2n) theorem](COMPACT_SYMPLECTIC_CHIRALITY.md) proves
all-element conjugacy to inverse and zero dual character for every
finite-dimensional complex source restricted along any subgroup homomorphism.
An invariant symmetric mass on that restriction preserves the zero dual
index. Thus a positive exact SM dual light target, tested through its faithful
gauge-weight evaluator, is impossible; an SU(5) chain is not required.
Mass invariance is needed only under the restricted group. No claim of
residual-charge-resolved self-duality follows from gauge self-duality.
This is a chirality obstruction within the stated finite mass class, separate
from the Abelian selection-rule theorem and from decay amplitudes. It does
not establish other compact-group classifications or composite chirality.

### Compact Spin Standard Chain

The [Spin(10) specialization](SPIN_STANDARD_CHAIN.md) constructs an actual
continuous injective SU(5) inclusion in the compact real Spin group and
applies the common standard-chain theorem with unchanged general model
inputs. Separately, the [actual half-spin 16](SPIN_HALF_SPIN.md) has proved
restricted character `1 + 10 + bar5` and an inhabited continuous model with
trivial residual action and zero mass. Its positive dual target is derived
from traces; its full torus/residual spectrum is one SM generation plus a
neutral singlet. Actual nonzero radical modes support the selection-rule
conclusion. Finite and continuous Abelian residual groups are included,
but their action in this benchmark is trivial.

The exact full-spectrum conclusion is specific to zero mass; the source's
dual target persists for any invariant symmetric mass on the restriction.
Neither result asserts an SM-only light space, realistic masses, an exact
SM vacuum, or a nonzero proton-decay amplitude. Other Spin(10) embeddings
and compact half-spin irreducibility are not proved by this benchmark.

### Non-Abelian Residual Coefficients

The [finite residual-group extension](../../../../topics/nonabelian-light-source/results.md)
retains actual ambient conjugations, finite-dimensional fields, invariant
symmetric mass and positive local targets, replacing scalar charge profiles
by actual finite-dimensional H representations. It derives nonzero ordered
qque/duql residual internal coefficients on actual radical weight spaces,
without assuming H Abelian or pre-supplying common light constituents.
The chosen slots are torus-neutral. Full SM gauge invariance on arbitrary
radicals and Lorentz/Grassmann nonvanishing are not consequences of that fact.
The old Abelian target is recovered coefficientwise on the common unitary
domain. This pair theorem remains finite-group-specific; the compact qque
extension below is separate. The existing infinite Abelian results are unchanged.
The [two-conjugation refinement](../../inputs/Physics/TWO_CONJUGATIONS.md) preserves the finite-group
pair and the Abelian full-support pair using two actual witnesses rather than
three. This uses the retained species-uniform target at all fifteen weights;
the Q-only qque endpoint separately drops down-target positivity.
The later [four-weight qque theorem](../Physics/FOUR_WEIGHT_QQUE.md) drops matching at
the other eleven weights for qque alone, in both routes. It retains the
opposite-weight dual terms, two conjugators and actual light support or
coefficients. It does not assert duql or full-five-species support.

The [compact continuous qque extension](../Physics/COMPACT_LIGHT_QQUE.md) removes finite H
for that four-weight endpoint. Joint continuity of the residual source action
and of the nonzero finite-dimensional Q target replaces finite-group input to
character counting and complete reducibility. H need not be Abelian or unitary
in the original inner product. Split quotients are derived on the original
light spaces. This extension still asserts an ordered internal functional,
not a full-gauge/Lorentz/Grassmann operator or a generated interaction.

With the additional [compatible full-SM decomposition](../Physics/EXPLICIT_SM_RESIDUAL_TENSOR.md),
the [spinor/exterior qque theorem](../Physics/LORENTZ_EXTERIOR_QQUE.md) constructs a nonzero
SM-cover x H x SL(2,C) invariant functional on the fourth exterior power of the
actual participating light-field sum. It includes algebraic fermionic
alternation, but not a generated quantum interaction or decay amplitude.
The extra full-SM decomposition is not inferred from the compact torus core.

## 6. Scope and limitations

### Explicitly unresolved / out of scope

`OUT-OF-SCOPE`

- exact structural cancellations without symmetry,
- arbitrary extra light chiral contributions changing the exact target index,
- SU(6) × U(1) and other product groups,
- generalized/non-invertible symmetries,
- ordinary non-Abelian protection beyond the finite pair and compact-continuous
  qque positive-target residual internal coefficient theorems above,
- R symmetries,
- Abelian actions that only normalize SU(6), act by a gauge automorphism, or
  require a compensating gauge transformation, except through the separately
  conditional gauge-twisted interfaces,
- identification of the dual Weyl/Majorana index with the signed Hermitian
  Dirac index; the checked symmetric-bilinear route does not make that claim,
- general Lagrangian semantics beyond the checked equivariant scalar-dependent
  symmetric mass/VEV data, and full non-Abelian proton-operator tensor realization
  beyond the declared torus/residual-group interface,
- negative-orientation profile targets and nonlinear Dirac-source wrappers,
- dynamically selected vacua or a proved exact-SM VEV stabilizer,
- higher-dimensional constructions,
- UV mechanisms outside the stated ordinary residual symmetry interfaces.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
