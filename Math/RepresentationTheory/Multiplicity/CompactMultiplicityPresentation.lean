import Math.RepresentationTheory.Characters.CompactCharacterPresentation
import Math.RepresentationTheory.Multiplicity.CompactMultiplicityIndex

/-! Normalized virtual indices derived from actual multiplicity spaces. -/

namespace Math.CompactMultiplicityPresentation
noncomputable section
open Representation ProductFactorization ContinuousRepresentationScope

universe uG uH uE uA uU
variable {G : Type uG} {H : Type uH} {E : Type uE} {A : Type uA}
  [Group G] [Group H] [Fintype A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {U : A → Type uU} [∀ a, AddCommGroup (U a)] [∀ a, Module ℂ (U a)]
  [∀ a, FiniteDimensional ℂ (U a)]
  (tau : Representation ℂ (G × H) E) (r : ∀ a, Representation ℂ G (U a))

abbrev Source : A ⊕ A → Type _
  | .inl a => MultiplicitySpace tau (r a)
  | .inr a => Module.Dual ℂ (MultiplicitySpace tau (r a).dual)

attribute [local instance] CompactMultiplicityIndex.normedAddCommGroup
  CompactMultiplicityIndex.normedSpace ContinuousDual.dualNormedAddCommGroup
  ContinuousDual.dualNormedSpace

instance sourceNormedAdd : (a : A ⊕ A) → NormedAddCommGroup (Source tau r a)
  | .inl a => inferInstanceAs (NormedAddCommGroup (MultiplicitySpace tau (r a)))
  | .inr a => inferInstanceAs
      (NormedAddCommGroup (Module.Dual ℂ (MultiplicitySpace tau (r a).dual)))

instance sourceNormedSpace : (a : A ⊕ A) → NormedSpace ℂ (Source tau r a)
  | .inl a => CompactMultiplicityIndex.normedSpace tau (r a)
  | .inr _a => ContinuousDual.dualNormedSpace

instance sourceFinite : (a : A ⊕ A) → FiniteDimensional ℂ (Source tau r a)
  | .inl a => inferInstanceAs (FiniteDimensional ℂ (MultiplicitySpace tau (r a)))
  | .inr a => inferInstanceAs
      (FiniteDimensional ℂ (Module.Dual ℂ (MultiplicitySpace tau (r a).dual)))

def sourceAction : (a : A ⊕ A) → Representation ℂ H (Source tau r a)
  | .inl a => multiplicityRepresentation tau (r a)
  | .inr a => (multiplicityRepresentation tau (r a).dual).dual

variable [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  (ht : IsJointlyContinuous (secondRestriction tau))

include ht in
omit [Fintype A] [CompactSpace H] in
theorem source_continuous (a : A ⊕ A) : IsJointlyContinuous (sourceAction tau r a) := by
  cases a with
  | inl a => exact CompactMultiplicityIndex.jointlyContinuous tau (r a) ht
  | inr a =>
    exact ContinuousDual.jointlyContinuous_dual _
      (CompactMultiplicityIndex.jointlyContinuous tau (r a).dual ht)

abbrev Index := CompactCharacterPresentation.Index (sourceAction tau r) (source_continuous tau r ht)
abbrev Carrier (i : Index tau r ht) :=
  CompactCharacterPresentation.Carrier (sourceAction tau r) (source_continuous tau r ht) i
abbrev action (i : Index tau r ht) :=
  CompactCharacterPresentation.action (sourceAction tau r) (source_continuous tau r ht) i

def coefficients (a : A) (i : Index tau r ht) : ℤ :=
  CompactCharacterPresentation.coefficients (sourceAction tau r)
    (source_continuous tau r ht) (.inl a) i -
  CompactCharacterPresentation.coefficients (sourceAction tau r)
    (source_continuous tau r ht) (.inr a) i

omit [Fintype A] in
theorem continuous (i : Index tau r ht) : IsJointlyContinuous (action tau r ht i) :=
  CompactCharacterPresentation.continuous _ _ i

omit [Fintype A] in
theorem inequivalent (i k : Index tau r ht) (hne : i ≠ k) :
    IsEmpty (Representation.Equiv (action tau r ht i) (action tau r ht k)) :=
  CompactCharacterPresentation.inequivalent _ _ i k hne

theorem index_character (a : A) (h : H) : CompactMultiplicityIndex.index tau (r a) h =
    CompactVirtualCharacter.character (action tau r ht) (coefficients tau r ht a) h :=
  CompactCharacterPresentation.difference (sourceAction tau r) (source_continuous tau r ht)
    (.inl a) (.inr a) h

theorem coefficient_hom_difference (a : A) (i : Index tau r ht) :
    (Module.finrank ℂ (IntertwiningMap (multiplicityRepresentation tau (r a))
      (action tau r ht i)) : ℤ) -
    (Module.finrank ℂ (IntertwiningMap (multiplicityRepresentation tau (r a).dual).dual
      (action tau r ht i)) : ℤ) = coefficients tau r ht a i := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  exact CompactVirtualCharacter.hom_difference (action tau r ht) (coefficients tau r ht a)
    (continuous tau r ht) (inequivalent tau r ht)
    (sourceAction tau r (.inl a)) (sourceAction tau r (.inr a))
    (source_continuous tau r ht _) (source_continuous tau r ht _)
    (index_character tau r ht a) i

def normalized : CompactCharacterPresentation.Presentation.{uH, max uE uU, uA}
    H (fun a => CompactMultiplicityIndex.index tau (r a)) where
  Index := Index tau r ht
  Carrier := Carrier tau r ht
  action := action tau r ht
  continuous := continuous tau r ht
  inequivalent := inequivalent tau r ht
  coefficients := coefficients tau r ht
  character := index_character tau r ht

end
end Math.CompactMultiplicityPresentation
