# Normalization From Actual Representation Differences

## Endpoint

[AutomaticSpeciesQque](../../../Physics/StandardModel/Operators/AutomaticSpeciesQque.lean)
provides `exists_actual_alternation` and `exists_actual_exterior` from the
retained ambient/mass carrier interface, a compatible jointly continuous
SM-cover x H action D on the unchanged radical K, compact H, and
`AutomaticSMSpeciesIndex.PairwisePositive j rho B D hd`.

There is no supplied irreducible family, integer profile, continuity or
inequivalence certificate for that family, or species-matching premise.
Those are constructed from the actual SM multiplicity representations.
The positivity predicate is evaluated on the constructed profiles: Q/up
share a positive component and Q/e share a possibly different one.
Positivity is still a premise, not a theorem for arbitrary light spectra.

No exact SM spectrum, conjugation, four-weight target or T-unitarity premise
was introduced. The source carrier/mass and compatible SM action requirements
of the direct pairwise route are unchanged. The result is a nonzero actual
qque alternating/exterior coefficient, not a generated Wilson coefficient,
nonzero decay amplitude or finite proton lifetime.

## Construction

1. [CompactCharacterPresentation](../../../Math/RepresentationTheory/Characters/CompactCharacterPresentation.lean)
   chooses finite semisimple decompositions of a finite family of actual
   continuous compact representations. Their irreducible subrepresentations
   inherit norms, finite dimension and continuity. A proved character-sum
   formula identifies the source character with the sum of its constituents.
2. [NormalizedCharacterFamily](../../../Math/RepresentationTheory/Characters/NormalizedCharacterFamily.lean)
   indexes representatives by the finite range of constituent characters.
   Equal characters are grouped and their integer coefficients are summed.
   Different indices have different characters, hence cannot be equivalent.
   The virtual character is unchanged. Actual copy coefficients are nonnegative
   and uniquely determined within the constructed family.
3. [CompactMultiplicityPresentation](../../../Math/RepresentationTheory/Multiplicity/CompactMultiplicityPresentation.lean)
   applies the construction simultaneously to actual species multiplicities
   and opposite-species contragredients. Subtracting copy coefficients gives
   signed indices. `index_character` proves the full character identity for
   every h. `coefficient_hom_difference` identifies each coefficient with the
   corresponding difference of actual intertwiner-space dimensions.
4. [AutomaticSMSpeciesIndex](../../../Physics/StandardModel/Spectrum/AutomaticSMSpeciesIndex.lean)
   specializes to the five standard species and derives the three equations
   consumed by the existing pairwise theorem. Using the existing gauge family
   from the exact-spectrum module adds no exact-spectrum assumption. The
   down/lepton indices are constructed too, but have no positivity condition.
5. The new operator entry supplies these derived inputs to the retained
   pairwise theorem. Actual fields, splitting maps, symmetrization and nonzero
   fermionic alternation remain derived results.

## Meaning And Limits

This removes the user's normalization/matching burden, not compactness,
continuity or the need for actual positive support. It does not license an
arbitrary coefficient table disconnected from K. The previous supplied-family
APIs remain available for hand-calculated presentations.

The construction is noncomputable: it proves and selects a finite presentation,
but is not a numerical decomposition program or a canonical ordering of
irreducibles. It can retain zero-coefficient components in a difference;
normalization means pairwise inequivalent irreducibles, not minimal support.
Coefficient uniqueness is proved for a fixed family; no separately packaged
comparison theorem between every possible presentation is claimed.

This is an application-interface improvement, not an exhibited larger class
of physical models or a new SU(5) benchmark. All dependency pins, ordinary
internal-symmetry scope and the E6 literature boundary remain unchanged.

## Audits

Persistent mathematical controls cover merging repeated constituents, signed
cancellation, a negative merged coefficient and an empty input family.
Both mathematical and physical audits check strict transitive axioms and
source-layer boundaries. See the [topic verification](README.md).
