import Physics.StandardModel.Spectrum.Representations.BalancedSpeciesExtension
import Physics.StandardModel.Operators.BaryonOne.Qque.AutomaticSpeciesQque

open Math

/-! Actual exterior qque for a balanced extension of an exact-SM reference.
Only the reference needs the exact spectrum and actual conjugators. -/

namespace Physics.BalancedSpeciesQque
noncomputable section
open Representation ProductFactorization InvariantWeylMass
open ContinuousRepresentationScope QqueSpinorExterior

variable {H G G₀ E E₀ : Type*} [Group H] [Group G] [Group G₀]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
  (j : SU5.MaximalTorus.Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)
  (j₀ : SU5.MaximalTorus.Torus →* G₀) (rho₀ : Representation ℂ (G₀ × H) E₀)
  (B₀ : SymmetricMass (rho₀.comp (j₀.prodMap (MonoidHom.id H))))
  (D₀ : LightSMAction.Compatible j₀ rho₀ B₀)
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  (hd : IsJointlyContinuous D.action)
  (ext : BalancedSpeciesExtension.Extension j rho B D j₀ rho₀ B₀ D₀)
  {n s : ℕ}
  (hs : ExactSMSpectrum.HasSpectrum (firstRestriction D₀.action) n s) (hn : 0 < n)
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation
    (ResidualWeightSpace.torus (rho₀.comp (j₀.prodMap (MonoidHom.id H)))))
  (c : StructuralConjugation.TwoConjugations j₀)

include hd ext hs hn hu c in
theorem exists_actual_alternation :
    ∃ fields : LightSMFieldExtraction.Fields D.action,
      HasNonzeroAlternation fields.Q.toRepresentation fields.U.toRepresentation
        fields.E.toRepresentation :=
  AutomaticSpeciesQque.exists_actual_alternation j rho B D hd
    (BalancedSpeciesExtension.pairwise_positive j rho B D j₀ rho₀ B₀ D₀ hd ext hs hn hu c)

include hd ext hs hn hu c in
theorem exists_actual_exterior : LightSMSpeciesQque.HasActualExterior j rho B D := by
  obtain ⟨fields, hf⟩ := exists_actual_alternation j rho B D j₀ rho₀ B₀ D₀ hd ext hs hn hu c
  exact ⟨fields, hf.exists_exterior⟩

end
end Physics.BalancedSpeciesQque
