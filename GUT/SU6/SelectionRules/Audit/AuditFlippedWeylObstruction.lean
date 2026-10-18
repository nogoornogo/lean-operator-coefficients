import GUT.SU6.Characters.CertifiedConstructions
import GUT.SU6.Adapters.CharacterQuotient

open Math

/-!
# Audit checklist for the flipped Weyl obstruction

This file collects the Lean-level witnesses for the seven critical audit points
listed in `PROOF_STATUS.md` for the flipped-branch obstruction.

The current fully checked scope is the obstructing `(3 6)` relative Weyl
generator.  This already excludes arbitrary finite virtual `SU(6)` restricted
characters at the level needed by the no-uplift argument, without assuming a
Laurent model for the source representations.  The wider statement for the
full relative `S₄` action and the independent Laurent-polynomial realization
of every intended continuous/smooth/algebraic finite-dimensional
representation remain separate tasks.
-/

namespace GUT
namespace AuditFlippedWeylObstruction

open VirtualRestriction

#print axioms FiniteVirtualSU6Representation.virtualRestriction_eq_restrictedCharacter

noncomputable section

universe u

abbrev EmbeddedFlippedTorus :=
  FlippedTorus.FlippedDiagonalSU6Point

abbrev NormalizedCoordinateRing :=
  Flipped.Normalized.Poly

/-- Audit point 1: the normalized coordinate ring has a faithful evaluator on the actual torus. -/
theorem audit1_normalized_coordinate_ring_faithful :
    NormalizedVirtualRestriction.DiagonalLaurentFaithful :=
  NormalizedVirtualRestriction.diagonalLaurentFaithful

/-- Audit point 2: the concrete `(3 6)` operation preserves the flipped weak-torus relation. -/
theorem audit2_swap36_preserves_embedded_torus
    (t : EmbeddedFlippedTorus) :
    (FlippedTorus.FlippedDiagonalSU6Point.swap36 t).toDiagonal.coords 3 *
        (FlippedTorus.FlippedDiagonalSU6Point.swap36 t).toDiagonal.coords 4 = 1 :=
  (FlippedTorus.FlippedDiagonalSU6Point.swap36 t).weak_relation

/-- Audit point 2: the matrix-level swap agrees with the Laurent-coordinate swap. -/
theorem audit2_swap36_matches_laurent_coordinates
    (t : EmbeddedFlippedTorus) :
    FlippedTorus.FlippedDiagonalSU6Point.toAlgebraicTorusPoint
        (FlippedTorus.FlippedDiagonalSU6Point.swap36 t) =
      Flipped.AlgebraicTorusPoint.swap36
        (FlippedTorus.FlippedDiagonalSU6Point.toAlgebraicTorusPoint t) :=
  FlippedTorus.FlippedDiagonalSU6Point.toAlgebraicTorusPoint_swap36 t

/-- Audit point 2: the concrete `U(3) x SU(2)` subgroup lifts every flipped torus point. -/
theorem audit2_concrete_flippedSM_embedding_lifts_torus
    (t : EmbeddedFlippedTorus) :
    FlippedSMGroup.embedding (FlippedSMGroup.torusPoint t) =
      t.toDiagonal.toSU6 :=
  FlippedSMGroup.embedding_torusPoint t

/-- Audit point 2: the concrete physical-group homomorphism is an embedding. -/
theorem audit2_concrete_flippedSM_embedding_injective :
    Function.Injective FlippedSMGroup.embedding :=
  FlippedSMGroup.embedding_injective

/-- Audit point 3: actual finite-dimensional restricted characters are `(3 6)`-invariant. -/
theorem audit3_actual_restricted_character_swap36_fixed
    (R : ActualSU6Representation) (t : EmbeddedFlippedTorus) :
    R.restrictedCharacter (FlippedTorus.FlippedDiagonalSU6Point.swap36 t) =
      R.restrictedCharacter t :=
  R.restrictedCharacter_swap36_fixed t

/-- Audit point 3 and 7: finite virtual restricted characters are `(3 6)`-invariant. -/
theorem audit3_finite_virtual_restricted_character_swap36_fixed
    (χ : FiniteVirtualSU6Representation) (t : EmbeddedFlippedTorus) :
    FiniteVirtualSU6Representation.restrictedCharacter χ
        (FlippedTorus.FlippedDiagonalSU6Point.swap36 t) =
      FiniteVirtualSU6Representation.restrictedCharacter χ t :=
  FiniteVirtualSU6Representation.restrictedCharacter_swap36_fixed χ t

/-- Audit point 3: any common faithful Laurent provider gives a fixed normalized polynomial. -/
theorem audit3_provider_polynomial_swap36_fixed
    {E : NormalizedVirtualRestriction.CommonLaurentEvaluator}
    (P : NormalizedVirtualRestriction.ActualLaurentModelProvider E)
    (χ : FiniteVirtualSU6Representation) :
    Flipped.Normalized.swap36
        (NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider
          P χ) =
      NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider
        P χ :=
  NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider_swap36_fixed
    P χ

/-- Audit point 4: the explicit list model equals the proposed factored flipped-SM character. -/
theorem audit4_legacy_flippedSM_factorization :
    Flipped.flippedSMCharacterExplicit = Flipped.flippedSMCharacter :=
  Flipped.flippedSM_factorization

/-- Audit point 4: the normalized target is its explicit 30-term expansion. -/
theorem audit4_normalized_flippedSM_explicit :
    Flipped.Normalized.flippedSMCharacterExplicit =
      Flipped.Normalized.flippedSMCharacter :=
  rfl

/--
Audit points 4 and 6: the normalized target is the canonical image of the
legacy factored character built from `C`, `Cbar`, and `W`.
-/
theorem audit4_normalized_target_matches_legacy_factorization :
    Flipped.Normalized.legacyFlippedSMCharacter =
      Flipped.Normalized.flippedSMCharacter :=
  Flipped.Normalized.legacyFlippedSMCharacter_eq_flippedSMCharacter

/-- The same bridge for the legacy term-by-term SM character. -/
theorem audit4_normalized_target_matches_legacy_expansion :
    Flipped.Normalized.legacyFlippedSMCharacterExplicit =
      Flipped.Normalized.flippedSMCharacterExplicit :=
  Flipped.Normalized.legacyFlippedSMCharacterExplicit_eq_flippedSMCharacterExplicit

/-- Audit point 5: the normalized flipped-SM target is not fixed by `(3 6)`. -/
theorem audit5_normalized_target_not_swap36_fixed :
    Flipped.Normalized.swap36 Flipped.Normalized.flippedSMCharacter ≠
      Flipped.Normalized.flippedSMCharacter :=
  Flipped.Normalized.swap36_flippedSMCharacter_ne

/--
Audit point 5: the non-invariance is visible on the actual flipped diagonal
`SU(6)` subtorus, so it is not an artifact killed by hidden quotient relations.
-/
theorem audit5_noninvariance_detected_on_actual_subtorus :
    ∃ t : EmbeddedFlippedTorus,
      NormalizedVirtualRestriction.diagonalLaurentEval
          (Flipped.Normalized.swap36 Flipped.Normalized.flippedSMCharacter) t ≠
        NormalizedVirtualRestriction.diagonalLaurentEval
          Flipped.Normalized.flippedSMCharacter t := by
  classical
  by_contra h
  apply Flipped.Normalized.swap36_flippedSMCharacter_ne
  apply NormalizedVirtualRestriction.diagonalLaurentFaithful
  intro t
  exact not_not.mp (by
    intro hneq
    exact h ⟨t, hneq⟩)

/-- Audit point 6: the color triplet character uses the first three color variables. -/
theorem audit6_colorTriplet_variables :
    Flipped.colorTriplet = Flipped.z1 + Flipped.z2 + Flipped.z3 :=
  rfl

/-- Audit point 6: the color antitriplet character uses the inverse color variables. -/
theorem audit6_colorAntiTriplet_variables :
    Flipped.colorAntiTriplet = Flipped.invZ1 + Flipped.invZ2 + Flipped.invZ3 :=
  rfl

/-- Audit point 6: the weak doublet character uses the weak pair `z4 + z5`. -/
theorem audit6_weakDoublet_variables :
    Flipped.weakDoublet = Flipped.z4 + Flipped.z5 :=
  rfl

/-- Audit point 6: `z5` is the inverse of the fourth SU(6) diagonal coordinate. -/
theorem audit6_z5_matches_actual_weak_inverse
    (t : EmbeddedFlippedTorus) :
    t.coordUnit 4 = (t.toAlgebraicTorusPoint).z5 :=
  t.coordUnit4_eq_z5

/-- Audit point 6: `z6` is the inverse product of the three color coordinates. -/
theorem audit6_z6_matches_actual_color_inverse
    (t : EmbeddedFlippedTorus) :
    t.coordUnit 5 = (t.toAlgebraicTorusPoint).z6 :=
  t.coordUnit5_eq_z6

/-- Audit point 6: the defining representation's six weights evaluate to the six coordinates. -/
theorem audit6_fundamental_weights_match_actual_coordinates
    (t : EmbeddedFlippedTorus) (i : WeylMatrix.I6) :
    Flipped.Exp.eval (FundamentalRepresentation.weight i)
        t.toAlgebraicTorusPoint =
      (t.coordUnit i : ℂ) :=
  FundamentalRepresentation.weight_eval_eq_coord t i

/--
Audit point 6 for the physical target: the five concrete field
representations and their duals evaluate to the canonical flipped-SM Laurent
character on the embedded torus.
-/
theorem audit6_physical_target_matches_canonical_character
    (t : EmbeddedFlippedTorus) :
    PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
        FlippedSMTarget.target (FlippedSMGroup.torusPoint t) =
      NormalizedVirtualRestriction.diagonalLaurentEval
        Flipped.Normalized.flippedSMCharacter t :=
  FlippedSMTarget.target_character_torus t

/--
Audit point 7: arbitrary finite virtual combinations with a common actual
Laurent provider cannot equal the normalized flipped-SM target.
-/
theorem audit7_no_arbitrary_provider_virtual_uplift
    {E : NormalizedVirtualRestriction.CommonLaurentEvaluator}
    (P : NormalizedVirtualRestriction.ActualLaurentModelProvider E) :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider
        P χ = Flipped.Normalized.flippedSMCharacter :=
  NormalizedVirtualRestriction.FiniteVirtualSU6Representation.no_flippedSM_uplift_of_actual_provider
    P

/--
Audit point 7, without a Laurent-provider hypothesis: no finite virtual
`SU(6)` restricted character agrees with the normalized flipped-SM target as a
function on the actual embedded flipped torus.
-/
theorem audit7_no_arbitrary_finite_virtual_character_uplift :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      ∀ t : EmbeddedFlippedTorus,
        FiniteVirtualSU6Representation.restrictedCharacter χ t =
          NormalizedVirtualRestriction.diagonalLaurentEval
            Flipped.Normalized.flippedSMCharacter t :=
  NormalizedVirtualRestriction.FiniteVirtualSU6Representation.no_restrictedCharacter_eq_flippedSMCharacter_eval

/--
Audit point 7 in restriction-image form: the target function is not in the
image of finite virtual `SU(6)` restricted characters.
-/
theorem audit7_target_not_mem_finite_virtual_restriction_image :
    NormalizedVirtualRestriction.FiniteVirtualSU6Representation.flippedSMCharacterEval
      ∉
    NormalizedVirtualRestriction.FiniteVirtualSU6Representation.finiteVirtualRestrictedCharacterImage :=
  NormalizedVirtualRestriction.FiniteVirtualSU6Representation.flippedSMCharacterEval_not_mem_finiteVirtualRestrictedCharacterImage

/-- Audit point 7 for the physical three-generation target. -/
theorem audit7_no_three_generation_finite_virtual_character_uplift :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      ∀ t : EmbeddedFlippedTorus,
        FiniteVirtualSU6Representation.restrictedCharacter χ t =
          NormalizedVirtualRestriction.diagonalLaurentEval
            (Flipped.Normalized.zscale 3
              Flipped.Normalized.flippedSMCharacter) t :=
  NormalizedVirtualRestriction.FiniteVirtualSU6Representation.no_restrictedCharacter_eq_nonzero_generation_flippedSMCharacter_eval
    3 (by norm_num)

/--
Audit point 7 for three generations plus an arbitrary integer virtual
multiplicity of gauge singlets.
-/
theorem audit7_no_three_generation_plus_singlets_uplift
    (singlets : ℤ) :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      ∀ t : EmbeddedFlippedTorus,
        FiniteVirtualSU6Representation.restrictedCharacter χ t =
          NormalizedVirtualRestriction.diagonalLaurentEval
            (Flipped.Normalized.zscale 3
                Flipped.Normalized.flippedSMCharacter +
              Flipped.Normalized.singletCharacter singlets) t :=
  NormalizedVirtualRestriction.FiniteVirtualSU6Representation.no_restrictedCharacter_eq_nonzero_generation_add_singlets_eval
    3 (by norm_num) singlets

/--
Audit point 7 at the physical-group boundary: once a concrete group
homomorphism `G -> SU(6)`, a lift of the flipped torus, and a physical virtual
target with the checked torus character are supplied, its character function
is outside the image of restricted finite virtual `SU(6)` representations.
-/
theorem audit7_physical_group_character_image_bridge
    {G : Type u} [Group G]
    {iota : G →* PhysicalRestrictionBridge.SU6}
    (L : PhysicalRestrictionBridge.FlippedTorusLift iota)
    (target :
      PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation G)
    (htarget : ∀ t,
      PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
          target (L.point t) =
        NormalizedVirtualRestriction.diagonalLaurentEval
          Flipped.Normalized.flippedSMCharacter t) :
    PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character target
        ∉
      Set.range (fun chi : FiniteVirtualSU6Representation =>
        PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
          (PhysicalRestrictionBridge.restrictVirtual iota chi)) :=
  PhysicalRestrictionBridge.flippedSMTarget_character_not_mem_restrictionImage
    L target htarget

/--
Audit point 7 with all physical data instantiated: the character of the
concrete one-generation `U(3) x SU(2)` target is outside the restriction image.
-/
theorem audit7_concrete_physical_target_not_mem_restriction_image :
    PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
        FlippedSMTarget.target ∉
      Set.range (fun chi : FiniteVirtualSU6Representation =>
        PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
          (PhysicalRestrictionBridge.restrictVirtual
            FlippedSMGroup.embedding chi)) :=
  FlippedSMTarget.flippedSMTarget_character_not_mem_restrictionImage

/-- Equivalent concrete statement using equality of whole-group characters. -/
theorem audit7_no_concrete_physical_characterEquivalent_restriction :
    ¬ ∃ chi : FiniteVirtualSU6Representation,
      PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.CharacterEquivalent
        (PhysicalRestrictionBridge.restrictVirtual FlippedSMGroup.embedding chi)
        FlippedSMTarget.target :=
  FlippedSMTarget.no_flippedSMTarget_characterEquivalent_restriction

/--
Audit point 7 after quotienting finite virtual presentations by equality of
whole-group characters.
-/
theorem audit7_concrete_target_not_mem_virtual_character_quotient_image :
    CharacterQuotient.mk FlippedSMTarget.target ∉
      Set.range
        (CharacterQuotient.restriction FlippedSMGroup.embedding) :=
  CharacterQuotient.flippedSMTarget_not_mem_quotientRestrictionImage

/--
Audit point 7: in the currently constructed tensor/exterior-generated
subquotient class, no finite virtual combination uplifts the flipped-SM target.
-/
theorem audit7_no_tensor_generated_subquotient_virtual_uplift :
    ¬ ∃ χ :
      CertifiedConstructions.FiniteTensorGeneratedSubquotientVirtualSU6Representation,
      CertifiedConstructions.FiniteTensorGeneratedSubquotientVirtualSU6Representation.normalizedPoly
        χ = Flipped.Normalized.flippedSMCharacter :=
  CertifiedConstructions.FiniteTensorGeneratedSubquotientVirtualSU6Representation.no_flippedSM_uplift

end

end AuditFlippedWeylObstruction
end GUT
