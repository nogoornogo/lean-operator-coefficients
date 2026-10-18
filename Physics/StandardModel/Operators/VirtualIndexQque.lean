import Physics.StandardModel.Spectrum.VirtualSMSpeciesIndex
import Physics.StandardModel.Operators.LightSMSpeciesQque

open Math

/-! Actual nonzero alternating qque from a common positive-dimensional virtual
index. Only one positive constituent is needed; the other coefficients may be
negative. No common quotient or coefficient is an input. -/

namespace GUT.VirtualIndexQque
noncomputable section
open Representation InvariantWeylMass ContinuousRepresentationScope
open SU5.MaximalTorus QqueSpinorExterior VirtualSMSpeciesIndex

variable {H G E I : Type*} [Group H] [Group G] [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  {V : I → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (S : ∀ i, Representation ℂ H (V i)) [∀ i, IsIrreducible (S i)]
  (a : Fin 5 → I → ℤ) (hc : ∀ i, IsJointlyContinuous (S i))
  (hn : ∀ i k, i ≠ k → IsEmpty (Representation.Equiv (S i) (S k)))

include hc hn in
theorem exists_actual_alternation_of_common_index
    (hd : IsJointlyContinuous D.action) (hs : SpeciesMatches j rho B D S a)
    (he : CompactVirtualCharacter.character S (a 0) = CompactVirtualCharacter.character S (a 1) ∧
      CompactVirtualCharacter.character S (a 0) = CompactVirtualCharacter.character S (a 4))
    (hp : 0 < CompactVirtualCharacter.dimension (V := V) (a 0)) :
    ∃ fields : LightSMFieldExtraction.Fields D.action,
      HasNonzeroAlternation fields.Q.toRepresentation fields.U.toRepresentation
        fields.E.toRepresentation := by
  let : MeasurableSpace (StandardSMGaugeTensor.GaugeGroup × H) := borel _
  let : BorelSpace (StandardSMGaugeTensor.GaugeGroup × H) := ⟨rfl⟩
  obtain ⟨fields⟩ := LightSMFieldExtraction.nonempty_fields D.action
    (CompactIrreducibleQuotient.semisimple D.action hd)
  obtain ⟨i, hv, ⟨sq⟩, ⟨su⟩, ⟨se⟩⟩ := common_quotient j rho B D S a hc hn hd hs he hp
  let : Nontrivial (V i) := hv
  exact ⟨fields, exists_on_fields sq su se
    fields.Q.toRepresentation fields.U.toRepresentation fields.E.toRepresentation
    fields.quarkEquiv fields.upEquiv fields.electronEquiv⟩

include hc hn in
theorem exists_actual_alternation
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (hd : IsJointlyContinuous D.action)
    (ht : WeightMatches j rho B S a) (hs : SpeciesMatches j rho B D S a)
    (hp : 0 < CompactVirtualCharacter.dimension (V := V) (a 0))
    (c : StructuralConjugation.TwoConjugations j) :
    ∃ fields : LightSMFieldExtraction.Fields D.action,
      HasNonzeroAlternation fields.Q.toRepresentation fields.U.toRepresentation
        fields.E.toRepresentation :=
  exists_actual_alternation_of_common_index j rho B D S a hc hn hd hs
    (characters_compatible j rho B S a hu ht c) hp

include hc hn in
theorem exists_actual_exterior
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (hd : IsJointlyContinuous D.action)
    (ht : WeightMatches j rho B S a) (hs : SpeciesMatches j rho B D S a)
    (hp : 0 < CompactVirtualCharacter.dimension (V := V) (a 0))
    (c : StructuralConjugation.TwoConjugations j) :
    LightSMSpeciesQque.HasActualExterior j rho B D := by
  obtain ⟨fields, hf⟩ := exists_actual_alternation j rho B D S a hc hn hu hd ht hs hp c
  exact ⟨fields, hf.exists_exterior⟩

end
end GUT.VirtualIndexQque
