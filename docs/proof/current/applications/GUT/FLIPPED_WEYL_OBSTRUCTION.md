# Flipped Weyl obstruction

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Representation-theoretic obstruction

The statements in this section are representation-theoretic obstructions to
realizing the flipped SM chiral character.  They are logically independent of
the standard-branch baryon-number and mixed-anomaly arguments in Abelian proton-operator neutrality and continuous U(1) anomaly cross-check.

#### Claim D1

`LEAN-CHECKED AT FINITE-VIRTUAL CHARACTER LEVEL; GROTHENDIECK PACKAGING REMAINS`

For flipped hypercharge

\[
6Y=\mathrm{diag}(1,1,1,0,0,-3),
\]

the SM chiral character is proposed to be **outside the restriction image** of the virtual SU(6) representation ring:

\[
F_{SM}^{flip}\notin \mathrm{Im}\bigl(R(SU(6))\to R(G_{SM})\bigr).
\]

This is stronger than merely proving that there is no anomaly-free uplift.

## 4. Proof structure

### Proposed argument D2

`LEAN-CHECKED FOR (3 6); FULL S4 UNVERIFIED`

Parameterize the flipped SM torus inside the SU(6) maximal torus by

\[
(z_1,z_2,z_3,z_4,z_5,z_6)
=(a_1t,a_2t,a_3t,b,b^{-1},t^{-3}),
\qquad a_1a_2a_3=1.
\]

The subtorus is preserved by permutations of indices \(\{1,2,3,6\}\), giving a proposed relative Weyl S4 action.

Any restricted SU(6) character must therefore be invariant under that S4 action.

**Lean update:** for the generator \((3\;6)\), `GUT/SU6/SelectionRules/FlippedBranch/Flipped.lean`
kernel-checks the exponent-lattice restriction identity
`AmbientExp.restrict_swap36` and the abstract bridge
`WeylInvariantCharacter.restricted_swap36_fixed`. It also checks
`FixedByConjugation.restricted_fixed_by_weyl_action`, the abstract step from
conjugacy-invariance to Weyl-invariance. `Math/RepresentationTheory/Decomposition/MathlibBridge.lean` now
imports mathlib's standard finite-dimensional representation theorem
`Representation.char_conj`, proving that `Representation.character` is
conjugacy-invariant for arbitrary groups, and specializes it to
`Matrix.specialUnitaryGroup (Fin 6) ℂ`. `GUT/SU6/Characters/WeylMatrix.lean` constructs a
determinant-one signed `(3 6)` permutation matrix in
`Matrix.specialUnitaryGroup (Fin 6) ℂ` and proves that conjugating a diagonal
maximal-torus element by this SU(6) element permutes the diagonal coordinates by
the modeled `(3 6)` action. `GUT/SU6/SelectionRules/FlippedBranch/ConcreteBridge.lean` connects this concrete
matrix calculation to `Flipped.AmbientPoint.swap36`, the action used in the
abstract restriction bridge. `GUT/SU6/Characters/ActualRestriction.lean` now packages
these pieces into the theorem `restrictedCharacter_swap36_fixed`: the restricted
character of any actual finite-dimensional complex representation of
`Matrix.specialUnitaryGroup (Fin 6) ℂ` is fixed under the concrete `(3 6)` Weyl
action on diagonal SU(6) torus points. It also proves
`LaurentRestrictedCharacterModel.swap36_fixed`: any faithful,
swap-compatible Laurent-polynomial model of such a restricted character is
fixed by `Flipped.swap36`. `GUT/SU6/Characters/VirtualRestriction.lean` extends the
character-level invariance to finite integer-linear combinations of actual
representations and proves that, once actual summands are supplied with Laurent
polynomials in a common faithful, swap-compatible evaluator, the finite virtual
combination has a `VirtualLaurentModel`. It also packages that hypothesis as
`ActualLaurentModelProvider` and proves
`FiniteVirtualSU6Representation.restrictedCharacter_has_faithful_swapCompatible_laurent_model`:
from such a provider, every finite virtual SU(6) restricted character has the
faithful, swap-compatible Laurent model needed for the obstruction. The
new file `GUT/SU6/Characters/LaurentEvaluation.lean` gives the current Laurent syntax an
explicit evaluation on the algebraic flipped torus `(ℂˣ)^4` and proves
`Poly.eval_zero`, `Poly.eval_add`, `Poly.eval_zscale`, and `Poly.eval_swap36`,
so the algebraic and swap-compatibility laws are now computational for that
algebraic-torus evaluator. `GUT/SU6/SelectionRules/FlippedBranch/FlippedTorus.lean` then defines the actual
flipped diagonal SU(6) subtorus, proves its sixth coordinate agrees with
`(z1*z2*z3)^-1`, and proves that the actual `(3 6)` Weyl action commutes with
the algebraic `(ℂˣ)^4` swap. `GUT/SU6/Characters/WeightTheory.lean` now constructs the
common evaluator on this actual flipped subtorus from a faithfulness theorem,
and proves a more concrete weight-theory bridge: a finite torus eigenbasis for
an actual SU(6) representation gives an `ActualTorusWeightCharacter`, hence a
Laurent polynomial whose evaluation is exactly the restricted trace character.
A choice of such eigenbases for all intended actual representations gives the
`ActualLaurentModelProvider` and a polynomial-level finite-virtual no-uplift
contradiction.

The normalized update below resolves the evaluator-faithfulness part of this
bridge.  The torus eigenbasis theorem is now also constructed for the explicit
hypercharge character rigidity analytic class by `CompactRepresentationUnitarization.lean`: every
finite-dimensional complex inner-product-space representation with jointly
continuous action obtains an equivalent Haar-averaged torus-unitary model and
hence a finite integral Laurent character.  Arbitrary abstract group
representations remain intentionally outside this statement, since they are
too broad to imply continuous Laurent-polynomial torus characters.

**Lean update:** `GUT/SU6/Characters/NormalizedLaurent.lean` now introduces the normalized
Laurent model `Flipped.Normalized.Poly := Exp →₀ ℤ`.  On the full algebraic
torus `(ℂˣ)^4`, Lean proves faithfulness of the evaluator via mathlib's
Dedekind linear independence theorem for distinct monoid characters
(`Flipped.Exp.linearIndependent_evalVecMonoidHom` and
`Flipped.Normalized.eval_faithful`).  The normalized evaluator is also checked
to be additive, integer-linear, and compatible with `swap36`, and the
normalized 30-term flipped SM character is proved non-invariant under `swap36`
by an explicit coefficient witness.  The file then rebuilds the finite-virtual
provider/no-uplift bridge over this normalized model and adds
`PhysicallyAdmissibleSU6Representation`, the current formal cut: an actual
finite-dimensional SU(6) representation together with a torus eigenbasis
certificate.  From such eigenbasis data, Lean constructs normalized restricted
Laurent characters and the corresponding normalized actual provider.

The exposed list syntax and the actual-subtorus faithfulness issue are now
separated and resolved in the normalized route: Lean proves unit-torus
faithfulness by Fourier monomials and realizes every unit-torus point as an
actual flipped diagonal SU(6) point.  Lean additionally proves
`FiniteVirtualSU6Representation.no_restrictedCharacter_eq_flippedSMCharacter_eval`:
no arbitrary finite virtual SU(6) restricted character agrees with the target
evaluation on that actual torus.  This theorem uses conjugacy invariance on the
source side and faithful Laurent evaluation only on the explicit target side,
so it does not require source-side torus eigenbasis certificates.  The
independent polynomial-level certificates are now available for the jointly
continuous finite-dimensional hypercharge character rigidity source scope through Haar averaging.
The equivalent theorem
`flippedSMCharacterEval_not_mem_finiteVirtualRestrictedCharacterImage` states
the conclusion directly as non-membership in the function-level restriction
image.
The generalized theorem
`no_restrictedCharacter_eq_nonzero_generation_flippedSMCharacter_eval` proves
the same obstruction for every nonzero integer multiple of one family; the
audit file instantiates it explicitly for three generations.  The further
theorem `no_restrictedCharacter_eq_nonzero_generation_add_singlets_eval`
allows any integer virtual multiplicity of gauge singlets, since their
character is `swap36`-fixed.

The concrete physical realization is now also checked.  The relevant global
form is modeled by `U(3) x SU(2)`, embedded as
`(A,B) |-> diag(A,B,det(A)^-1)`.  Its physical one-generation target is the
finite virtual sum of `R - R*` for `Q = 3 tensor 2`,
`Uc = 3* tensor det^-1`, `Dc = 3* tensor det`,
`L = 2 tensor det^-1`, and `Ec = det^2`.  Lean proves that its trace character
on the lifted flipped torus is the legacy termwise expression and therefore
the canonical normalized target.

**Lean update:** `GUT/SU6/SelectionRules/FlippedBranch/PhysicalRestrictionBridge.lean` now constructs that
forward map for an arbitrary group homomorphism `G -> SU(6)`: actual
representations are restricted by composition, finite virtual restrictions are
formed termwise, and their characters are proved to commute with evaluation on
any lifted flipped torus.  Consequently, any concrete target virtual
`G`-representation with the checked flipped-SM torus character has a character
function outside the restriction character image.

**Lean update:** `GUT/SU6/SelectionRules/FlippedBranch/FlippedSMGroup.lean` constructs the concrete
`U(3) x SU(2) -> SU(6)` block embedding and a lift of every flipped torus
point.  `GUT/SU6/SelectionRules/FlippedBranch/FlippedSMTarget.lean` constructs the five actual field
representations above using defining, dual, tensor-product, and determinant
representations.  It proves `target_character_torus`, then specializes the
forward bridge to the unconditional theorems
`no_flippedSMTarget_characterEquivalent_restriction` and
`flippedSMTarget_character_not_mem_restrictionImage`.  Thus the only remaining
step for conventional `R(G_SM)` notation is its identification with the
character quotient used here; it is not needed for the checked finite-virtual
character-image statement.

**Lean update:** `GUT/SU6/Adapters/CharacterQuotient.lean` now quotients finite virtual
presentations by equality of their whole-group characters, proves restriction
is well-defined on these quotients, and proves the physical target quotient
class is outside the restriction image.  This supplies an actual quotient-level
statement.  The file intentionally does not rename this object a Grothendieck
representation ring: connecting the conventional compact-group construction
to this character quotient requires the independent character-classification
theorem.

**Lean update:** `GUT/SU6/Representations/FundamentalRepresentation.lean` now constructs the
defining six-dimensional `SU(6)` representation as an actual matrix
representation, proves that the standard basis is a flipped-torus eigenbasis,
and identifies its six weights as
`z1, z2, z3, z4, z4^-1, (z1*z2*z3)^-1`.  This gives a concrete
`PhysicallyAdmissibleSU6Representation` whose restricted character is checked
against the common faithful normalized Laurent evaluator.

**Lean update:** `GUT/SU6/Characters/CertifiedConstructions.lean` proves that torus
eigenbasis certificates are preserved by trivial representations,
representation isomorphisms, direct sums/products, tensor products, exterior
powers, duals, stable coordinate subrepresentations, and stable coordinate
quotients.  It also defines `TensorGeneratedSU6Representation`, the current
Lean-certified intended class generated from the defining representation by
these ring-style operations, now including exterior powers.  For finite virtual
combinations of this class, Lean proves that the normalized Laurent polynomial
is fixed by `swap36` and therefore cannot equal the normalized flipped SM
character.  The file now also defines tensor/exterior-generated subquotient
certificates: an actual representation may be accepted when it is isomorphic to
an `SU(6)`-stable coordinate subrepresentation or coordinate quotient of such
an ambient tensor construction.  Finite virtual sums of these certified
subquotients inherit the same normalized Laurent model and no-uplift
contradiction.  It is unnecessary to prove that every continuous
finite-dimensional representation is generated by these explicit
subquotients: compact Haar averaging now gives the required Laurent model
directly for the jointly continuous analytic scope.  The generated class is
retained as a constructive alternative, and the stronger function-level
no-uplift theorem above remains independent of either certificate route.

#### Proposed argument D3

`LEAN-CHECKED`

Define the chiral character of the fundamental virtual representation:

\[
D_6=\chi_6-\chi_{\bar6}
=Ct-\bar C t^{-1}+t^{-3}-t^3.
\]

The one-family SM chiral character is proposed to factor exactly as

\[
F_{SM}=D_6\left(W-t^3-t^{-3}\right).
\]

The second factor becomes

\[
A=z_4+z_5-z_6-z_6^{-1}.
\]

Under a permutation such as \((3\;6)\), \(A\) is not invariant while \(D_6\) is invariant. Because the torus character ring is an integral domain, the product cannot be invariant unless A is invariant. This is the proposed contradiction.

**Lean update:** `GUT/SU6/SelectionRules/FlippedBranch/Flipped.lean` verifies the factorization and proves
directly that the full \(F_{SM}\) is not fixed by \((3\;6)\). This avoids
depending on the integral-domain cancellation step for the first milestone.
`GUT/SU6/Characters/ActualRestriction.lean` further proves that no faithful,
swap-compatible Laurent model of an actual finite-dimensional SU(6)
representation can equal either `flippedSMCharacter` or
`flippedSMCharacterExplicit`.

#### Critical audit points for flipped critical audit

1. Precisely define the embedded torus and its coordinate ring.
2. Prove the claimed permutation really preserves the embedded torus relevant to the flipped SM subgroup.
3. Prove every restriction of an SU(6) virtual character is invariant under that relative Weyl action.
4. Verify the explicit factorization of the SM chiral character.
5. Verify that no quotient relation in the coordinate ring invalidates the integral-domain cancellation step.
6. Verify that color and weak characters C, \bar C, W have been represented consistently with the torus variables.
7. Verify that the proof excludes arbitrary finite-dimensional virtual combinations, not only low-dimensional irreps.

No final theorem should be accepted until all seven items are explicit.

**Lean audit update:** `GUT/SU6/SelectionRules/Audit/AuditFlippedWeylObstruction.lean` now collects explicit named
checks for these seven items in the currently formalized scope: the obstructing
relative Weyl generator `(3 6)` and the normalized faithful Laurent model.
Items 1, 2, 4, 5, and 6 are checked directly by definitions/theorems for the
actual flipped diagonal torus, normalized coordinate ring, explicit flipped-SM
target, coordinate identifications, and a kernel-checked equality between that
normalized target and the normalization of the legacy factored/termwise SM
characters.  Items 3 and 7 are now checked directly
for arbitrary finite virtual `SU(6)` representations at the level of equality
of restricted-character functions on the actual flipped torus; no Laurent
provider or torus-eigenbasis certificate for the source representations is
needed for this exclusion.  Provider-based polynomial equality and the current
tensor/exterior-generated subquotient certificate class are also checked as
stronger structured variants.  Haar averaging now constructs Laurent models
for the jointly continuous finite-dimensional analytic scope independently,
but this is not a hypothesis of the `(3 6)` no-uplift contradiction.
Extending the formalized action from the single obstructing generator `(3 6)`
to the full relative `S4` is optional for this contradiction.  The audit
additionally exposes the general physical
group forward bridge as `audit7_physical_group_character_image_bridge` and its
fully instantiated conclusion as
`audit7_concrete_physical_target_not_mem_restriction_image`.  All seven points
are therefore explicit for the one obstructing generator and the concrete
physical target.  Literal quotient notation for the representation ring is a
packaging task beyond these seven checks, not a missing implication in them.
The virtual-character quotient and its restriction non-membership theorem are
already checked as
`audit7_concrete_target_not_mem_virtual_character_quotient_image`.

---

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
