# Kernel-checked flipped-character chain

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. Restricted finite virtual
SU(6) characters cannot equal the specified flipped-SM target in the established
function-level and modeled interfaces.

## 2. Inputs And Conclusion

Actual finite-dimensional representations and finite integer sums are
distinguished from polynomial-provider and eigenbasis certificate interfaces.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Conjugacy fixes restricted characters under the signed transposition; faithful
Laurent evaluation detects the target non-invariance.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### General Restriction API

`Math/RepresentationTheory/Characters/CharacterRestriction.lean` extracts the generic
conjugation, finite-virtual invariance, and faithful-target obstruction steps.
It imports only mathlib and uses actual representations, with finite integer
coefficients in `Finsupp`. The existing SU(6) finite presentations have a
proved character-preserving adapter to its `FDRep` coefficient model; the
existing actual/virtual invariance and normalized no-uplift theorems now use
the general API. The statements of those SU(6) endpoints are unchanged.
See [the generalization dossier](../../../inputs/Math/CHARACTER_RESTRICTION.md) for scope,
declarations, and the persistent independent audit.

#### Kernel-checked

- `GUT.Flipped.flippedSM_factorization`
  - verifies the explicit one-generation flipped SM chiral character equals
    `D6 * A` in the Laurent character ring of the flipped subtorus.
- `GUT.Flipped.weak_relation_z4_z5` and
  `GUT.Flipped.su6_torus_relation`
  - verify the coordinate model relations `z4*z5 = 1` and
    `z1*z2*z3*z4*z5*z6 = 1`.
- `GUT.Flipped.swap36_preserves_weak_relation` and
  `GUT.Flipped.swap36_preserves_su6_torus_relation`
  - verify the modeled `(3 6)` action preserves those two torus relations.
- `GUT.Flipped.AmbientExp.restrict_swap36`
  - verifies that the ambient SU(6) rank-5 exponent-lattice transposition
    `(3 6)` commutes with restriction to the flipped rank-4 exponent lattice.
- `GUT.Flipped.WeylInvariantCharacter.restricted_swap36_fixed`
  - proves the abstract bridge: any ambient character fixed by `(3 6)`
    restricts to a character fixed by the induced `(3 6)` action on any
    preserved subtorus.
- `GUT.Flipped.FixedByConjugation.restricted_fixed_by_weyl_action`
  - proves the conjugacy-invariance route to the bridge: if a Weyl action on a
    torus is implemented by conjugation in the ambient group and a class
    function is fixed by that conjugation, then its torus restriction is fixed by
    the Weyl action.
- `GUT.Flipped.AmbientPoint.ext`
  - gives an extensionality lemma for the six-coordinate ambient torus point
    model.
- `GUT.Flipped.TraceRepresentation.character_conjugation_fixed`
  - proves, in a small local trace algebra abstraction, that trace characters
    are invariant under conjugation once cyclicity of trace and the
    representation multiplication/inverse laws are supplied.
- `GUT.MathlibBridge.representation_character_conj`
  - imports the corresponding standard mathlib theorem for arbitrary
    finite-dimensional group representations: `Representation.character` is
    constant on conjugacy classes.
- `GUT.MathlibBridge.su6_representation_character_conj`
  - specializes that theorem to the concrete mathlib group
    `Matrix.specialUnitaryGroup (Fin 6) ℂ`.
- `GUT.WeylMatrix.signedSwap36_mem_specialUnitary`
  - constructs a signed `(3 6)` permutation matrix and verifies it lies in
    `Matrix.specialUnitaryGroup (Fin 6) ℂ`.
- `GUT.WeylMatrix.signedSwap36SU_conj_diagonal` and
  `GUT.WeylMatrix.signedSwap36SU_conj_diagonal_entry`
  - verify that conjugating a diagonal maximal-torus element by that SU(6)
    representative permutes diagonal coordinates by the modeled `(3 6)` swap.
- `GUT.ConcreteBridge.ambientPointOfDiag_swap36` and
  `GUT.ConcreteBridge.concrete_matrix_realizes_swap36WeylActionData`
  - connect the concrete matrix-level coordinate permutation to the
    `Flipped.AmbientPoint.swap36` action used by the abstract bridge.
- `GUT.ActualRestriction.restrictedCharacter_swap36_fixed`
  - proves unconditionally that the restricted character of any actual
    finite-dimensional complex representation of
    `Matrix.specialUnitaryGroup (Fin 6) ℂ` is fixed under the concrete `(3 6)`
    Weyl action on diagonal SU(6) torus points.
- `GUT.ActualRestriction.restrictedCharacter_swap36_fixed_via_bridge`
  - proves the same statement through the abstract
    `FixedByConjugation.restricted_fixed_by_weyl_action` bridge.
- `GUT.ActualRestriction.LaurentRestrictedCharacterModel.swap36_fixed`
  - proves that any faithful Laurent-polynomial model of such an actual
    restricted SU(6) character, with swap-compatible evaluation, is fixed by
    `Flipped.swap36`.
- `GUT.ActualRestriction.LaurentRestrictedCharacterModel.poly_ne_flippedSMCharacter`
  and `poly_ne_flippedSMCharacterExplicit`
  - prove that such a faithful Laurent model for an actual representation
    cannot equal the flipped SM character checked earlier.
- `GUT.FlippedTorus.FlippedDiagonalSU6Point`
  - defines the actual flipped diagonal SU(6) subtorus used by the Laurent
    evaluator, with relation `z4*z5 = 1`.
- `GUT.FlippedTorus.FlippedDiagonalSU6Point.det_product`,
  `coord_ne_zero`, `coord5_eq_inv_colorProduct`, and `coordUnit5_eq_z6`
  - prove that points of this subtorus have nonzero coordinates and that the
    sixth coordinate is forced to be `(z1*z2*z3)^-1`, matching the Laurent
    model's `z6`.
- `GUT.FlippedTorus.FlippedDiagonalSU6Point.toAlgebraicTorusPoint_swap36`
  - proves the actual flipped diagonal subtorus map to `(ℂˣ)^4` commutes with
    the concrete `(3 6)` Weyl action.
- `GUT.FlippedTorus.FlippedDiagonalSU6Point.restrictedCharacter_swap36_fixed`
  - transports actual SU(6) restricted-character invariance to the flipped
    diagonal subtorus.
- `GUT.VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter_swap36_fixed`
  - proves that the restricted character of any finite integer-linear
    combination of actual finite-dimensional SU(6) representations is fixed
    under the concrete `(3 6)` Weyl action on flipped diagonal SU(6) subtorus
    points.
- `GUT.VirtualRestriction.modeledFiniteVirtual_has_laurent_model`
  - proves that a finite virtual combination whose actual summands have Laurent
    polynomials in one common faithful, swap-compatible evaluator has a
    `VirtualLaurentModel`.
- `GUT.VirtualRestriction.ActualLaurentModelProvider`
  - packages the source-polynomial realization input: every actual summand is
    assigned a Laurent polynomial in the same faithful, swap-compatible
    evaluator.
- `GUT.VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter_has_faithful_swapCompatible_laurent_model`
  - proves that, from such a provider, every finite virtual SU(6)
    representation has a faithful, swap-compatible Laurent model for its
    restricted character.
- `GUT.VirtualRestriction.VirtualLaurentModel.swap36_fixed`
  - proves that every such virtual Laurent model is fixed by `Flipped.swap36`.
- `GUT.VirtualRestriction.modeledFiniteVirtual_poly_ne_flippedSMCharacter`
  and `modeledFiniteVirtual_poly_ne_flippedSMCharacterExplicit`
  - prove that the modeled finite virtual polynomial cannot equal either the
    factored or expanded flipped SM character.
- `GUT.VirtualRestriction.FiniteVirtualSU6Representation.no_flippedSM_uplift_of_actual_provider`
  and `no_flippedSMExplicit_uplift_of_actual_provider`
  - prove the finite-virtual no-uplift contradiction under the provider
    hypothesis.
- `GUT.Flipped.AlgebraicTorusPoint.swap36_involutive`
  - verifies that the algebraic flipped-torus `(3 6)` operation is an
    involution on the four independent Laurent coordinates.
- `GUT.Flipped.Exp.eval_swap36Exp`
  - proves monomial evaluation is compatible with the exponent-level
    `swap36Exp` action.
- `GUT.Flipped.Poly.eval_zero`, `Poly.eval_add`, `Poly.eval_sub`,
  `Poly.eval_mul`, `Poly.eval_zscale`, and `Poly.eval_swap36`
  - give the current Laurent-polynomial syntax an explicit evaluation on
    `(ℂˣ)^4` and prove the evaluator respects the polynomial operations and is
    swap-compatible.
- `GUT.Flipped.RawCharacter.eval_toPoly`
  - proves that evaluating a finite raw weight character agrees with evaluating
    its normalized finite-list Laurent polynomial.
- `GUT.WeightTheory.commonLaurentEvaluatorOfFaithful`
  - constructs the common swap-compatible evaluator on the actual flipped
    diagonal subtorus from the algebraic `(ℂˣ)^4` evaluator and a faithfulness
    theorem for that evaluator.
- `GUT.WeightTheory.trace_eq_sum_of_basis_eigen`
  - proves the linear-algebra trace calculation: if a linear map is diagonal in
    a finite basis with eigenvalues `weightValue i`, its trace is the finite
    sum of those eigenvalues.
- `GUT.WeightTheory.TorusEigenbasis.toActualTorusWeightCharacter`
  - constructs the restricted Laurent character of an actual SU(6)
    representation from a finite torus eigenbasis certificate.
- `GUT.WeightTheory.torusWeightTheoryOfEigenbasisTheory` and
  `actualLaurentModelProviderOfEigenbasisTheory`
  - show that a torus-eigenbasis theorem for every actual representation gives
    the `ActualLaurentModelProvider` used by the polynomial-level route.
- `GUT.WeightTheory.finiteVirtual_has_laurent_model_of_eigenbasisTheory`,
  `no_flippedSM_uplift_of_eigenbasisTheory`, and
  `no_flippedSMExplicit_uplift_of_eigenbasisTheory`
  - prove the finite-virtual no-uplift consequences from this eigenbasis-level
    weight-theory input plus evaluator faithfulness.
- `GUT.Flipped.Normalized.Poly`
  - introduces the normalized Laurent model `Exp →₀ ℤ`, replacing exposed
    finite-list syntax by finitely supported exponent coefficients.
- `GUT.Flipped.Exp.linearIndependent_evalVecMonoidHom`
  - proves linear independence of the Laurent monomial characters on
    `(ℂˣ)^4` using mathlib's Dedekind linear-independence theorem for distinct
    monoid homomorphisms.
- `GUT.Flipped.Normalized.eval_faithful`
  - proves the normalized Laurent evaluator on the algebraic torus `(ℂˣ)^4`
    is faithful.
- `GUT.Flipped.Normalized.evalUnitAddTorus_faithful`
  - proves the same normalized Laurent faithfulness on the compact unit torus
    `UnitAddTorus (Fin 4)`, using mathlib's Fourier monomials.
- `GUT.Flipped.Normalized.eval_zero`, `eval_add`, `eval_zscale`, and
  `eval_swap36`
  - prove the normalized evaluator is additive, integer-linear, and compatible
    with the modeled `swap36` action.
- `GUT.Flipped.Normalized.swap36_flippedSMCharacter_ne`
  - proves the normalized 30-term flipped SM character is not fixed by
    `swap36`, witnessed by a concrete coefficient change.
- `GUT.Flipped.Normalized.legacyFlippedSMCharacter_eq_flippedSMCharacter`
  and `legacyFlippedSMCharacterExplicit_eq_flippedSMCharacterExplicit`
  - verify that the canonical 30-term target is exactly the normalization of
    both the legacy factored character and its term-by-term SM expansion.
- `GUT.Flipped.Normalized.eval_ofListPoly`
  - proves that passage from the legacy list syntax to the normalized
    `Finsupp` model preserves Laurent evaluation.
- `GUT.FlippedTorus.FlippedDiagonalSU6Point.ofUnitAddTorus`
  and `toAlgebraicTorusPoint_ofUnitAddTorus`
  - realize every four-coordinate unit-torus point as an actual flipped
    diagonal SU(6) point and prove its Laurent coordinates are the expected
    unit-circle coordinates.
- `GUT.NormalizedVirtualRestriction.diagonalLaurentFaithful`
  - transports unit-torus Fourier faithfulness to the actual flipped diagonal
    SU(6) subtorus.
- `GUT.NormalizedVirtualRestriction.FiniteVirtualSU6Representation.no_restrictedCharacter_eq_flippedSMCharacter_eval`
  - proves directly that no arbitrary finite virtual SU(6) restricted
    character equals the normalized flipped-SM target as a function on the
    actual flipped torus; this requires no Laurent provider or eigenbasis
    certificate for the source representations.
- `GUT.NormalizedVirtualRestriction.FiniteVirtualSU6Representation.flippedSMCharacterEval_not_mem_finiteVirtualRestrictedCharacterImage`
  - packages the same result as literal non-membership in the `Set.range` of
    the finite-virtual restricted-character map.
- `GUT.NormalizedVirtualRestriction.FiniteVirtualSU6Representation.no_restrictedCharacter_eq_nonzero_generation_flippedSMCharacter_eval`
  - extends the function-level obstruction to every nonzero integer multiple
    of the one-generation target; the flipped critical audit audit includes the physical
    three-generation specialization.
- `GUT.NormalizedVirtualRestriction.FiniteVirtualSU6Representation.no_restrictedCharacter_eq_nonzero_generation_add_singlets_eval`
  - proves the same result after adding any integer virtual multiplicity of
    gauge singlets; the audit records its three-generation specialization.
- `GUT.PhysicalRestrictionBridge.restrictActual`, `restrictVirtual`, and
  `restrictVirtual_character_on_torus`
  - construct restriction along an arbitrary group homomorphism `G -> SU(6)`
    by composing actual representations and prove that finite virtual
    characters commute with evaluation on any lifted flipped torus.
- `GUT.PhysicalRestrictionBridge.flippedSMTarget_character_not_mem_restrictionImage`
  - proves that any concrete target virtual `G`-representation with the checked
    flipped-SM torus character has a whole-group character function outside the
    image of restricted finite virtual `SU(6)` characters.  This forward bridge
    uses no injectivity or character-separation theorem.
- `GUT.FlippedSMGroup.embedding` and `flippedTorusLift`
  - construct the concrete global flipped subgroup `U(3) x SU(2)` with block
    embedding `(A,B) |-> diag(A,B,det(A)^-1)` into `SU(6)`, and prove every
    point of the flipped torus lifts through it; `embedding_injective` proves
    the group homomorphism is injective.
- `GUT.FlippedSMTarget.Q`, `Uc`, `Dc`, `L`, `Ec`, and `target`
  - construct the five physical field representations and the one-generation
    chiral finite virtual target from defining, dual, tensor-product, and
    determinant representations.
- `GUT.FlippedSMTarget.target_character_torus`
  - computes the target trace character on the actual lifted torus and proves
    it equals the canonical normalized 30-term Laurent character.
- `GUT.FlippedSMTarget.no_flippedSMTarget_characterEquivalent_restriction`
  and `flippedSMTarget_character_not_mem_restrictionImage`
  - prove, with all group and target data instantiated, that no finite virtual
    `SU(6)` restriction has the same whole-group character as the physical
    one-generation target.
- `GUT.CharacterQuotient.restriction` and
  `flippedSMTarget_not_mem_quotientRestrictionImage`
  - quotient source and target finite virtual presentations by whole-group
    character equality, descend restriction to that quotient, and prove the
    concrete physical target class is outside its image.
- `GUT.NormalizedVirtualRestriction.commonLaurentEvaluatorOfFaithful`
  `commonLaurentEvaluator`, and
  `FiniteVirtualSU6Representation.polyOfProvider_swap36_fixed`
  - rebuild the finite-virtual provider bridge over the normalized Laurent
    model.
- `GUT.WeightTheory.PhysicallyAdmissibleSU6Representation`
  - records the current formal cut for physically intended representations:
    an actual finite-dimensional SU(6) representation equipped with a torus
    eigenbasis certificate, instead of an arbitrary abstract representation.
- `GUT.WeightTheory.TorusEigenbasis.toActualNormalizedTorusWeightCharacter`
  and `actualNormalizedLaurentModelProviderOfEigenbasisTheory`
  - construct normalized Laurent polynomials for restricted actual characters
    from torus eigenbasis data.
- `GUT.WeightTheory.no_flippedSM_normalized_uplift_of_eigenbasisTheory`
  - proves the normalized finite-virtual no-uplift consequence from the
    eigenbasis-level input plus normalized diagonal evaluator faithfulness.
- `GUT.WeightTheory.actualNormalizedLaurentModelProvider` and
  `no_flippedSM_normalized_uplift`
  - specialize the previous result using the kernel-checked normalized
    diagonal faithfulness theorem; the polynomial-level route retains the
    eigenbasis-level weight-theory hypothesis.
- `GUT.Flipped.swap36WeylActionData_z3`,
  `GUT.Flipped.swap36WeylActionData_z6`, and
  `GUT.Flipped.swap36WeylActionData_z4`
  - verify the abstract point-level Weyl action data sends the relevant torus
    coordinates exactly as the modeled `(3 6)` permutation requires.
- `GUT.Flipped.restrict_ambientSwap36` and
  `GUT.Flipped.restrict_fixed_of_ambient_fixed`
  - verify the finite Laurent-monomial model commutes with ambient `(3 6)`
    restriction and inherits fixedness termwise.
- `GUT.Flipped.finite_laurent_model_exists`
  - verifies every finite raw ambient Laurent character has an explicit
    restricted Laurent-polynomial image in the current finite-list model.
- `GUT.Flipped.swap36_D6`
  - verifies the transposition `(3 6)` fixes `D6`.
- `GUT.Flipped.swap36_A_ne`
  - verifies `(3 6)` does not fix `A`.
- `GUT.Flipped.swap36_flippedSM_ne`
  - verifies the factored flipped SM character is not fixed by `(3 6)`.
- `GUT.Flipped.swap36_flippedSMExplicit_ne`
  - verifies the expanded flipped SM character is not fixed by `(3 6)`.
- `GUT.Flipped.no_flipped_sm_uplift_conditional`
  - proves that, assuming every restricted finite virtual SU(6) character is
    fixed by the modeled `(3 6)` action, the flipped SM character is not in the
    restriction image.

## 6. Scope And Limitations

Provider-based corollaries retain their provider premise; character obstruction
is not a decay or vacuum theorem.

## 7. Sources And Verification

The [scope dossier](../FLIPPED_WEYL_OBSTRUCTION.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.
