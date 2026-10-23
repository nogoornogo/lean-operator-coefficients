import Physics.StandardModel.Spectrum.Representations.PairwisePositiveSpeciesIndex
import Physics.StandardModel.Operators.BaryonOne.Qque.PairwiseQqueSpinorExterior
import Physics.StandardModel.Operators.BaryonOne.Qque.LightSMSpeciesQque

open Math

namespace Physics.PairwisePositiveQque
noncomputable section
open Representation InvariantWeylMass ContinuousRepresentationScope
open SU5.MaximalTorus QqueSpinorExterior PairwisePositiveSpeciesIndex

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
theorem exists_actual_alternation
    (hd : IsJointlyContinuous D.action)
    (hs : VirtualSMSpeciesIndex.SpeciesMatches j rho B D S a)
    (hp : PairwisePositive a) :
    ∃ fields : LightSMFieldExtraction.Fields D.action,
      HasNonzeroAlternation fields.Q.toRepresentation fields.U.toRepresentation
        fields.E.toRepresentation := by
  let : MeasurableSpace (StandardSMGaugeTensor.GaugeGroup × H) := borel _
  let : BorelSpace (StandardSMGaugeTensor.GaugeGroup × H) := ⟨rfl⟩
  obtain ⟨fields⟩ := LightSMFieldExtraction.nonempty_fields D.action
    (CompactIrreducibleQuotient.semisimple D.action hd)
  obtain ⟨i, k, hv, hw, ⟨qr⟩, ⟨ur⟩, ⟨qs⟩, ⟨es⟩⟩ :=
    pairwise_quotients S a hc hn j rho B D hd hs hp
  let : Nontrivial (V i) := hv
  let : Nontrivial (V k) := hw
  exact ⟨fields, PairwiseQqueSpinorExterior.exists_on_fields qr ur qs es
    fields.Q.toRepresentation fields.U.toRepresentation fields.E.toRepresentation
    fields.quarkEquiv fields.upEquiv fields.electronEquiv⟩

include hc hn in
theorem exists_actual_exterior
    (hd : IsJointlyContinuous D.action)
    (hs : VirtualSMSpeciesIndex.SpeciesMatches j rho B D S a)
    (hp : PairwisePositive a) : LightSMSpeciesQque.HasActualExterior j rho B D := by
  obtain ⟨fields, hf⟩ := exists_actual_alternation j rho B D S a hc hn hd hs hp
  exact ⟨fields, hf.exists_exterior⟩

end
end Physics.PairwisePositiveQque
