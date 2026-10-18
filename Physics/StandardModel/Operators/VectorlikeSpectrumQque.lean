import Physics.StandardModel.Operators.BalancedSpeciesQque
import Math.RepresentationTheory.Multiplicity.VectorlikeMultiplicity

open Math

/-! A global SM x H vectorlike decomposition derives all three balanced
species decompositions; they are not additional user certificates. -/

namespace GUT.VectorlikeSpectrumQque
noncomputable section
open Representation ProductFactorization InvariantWeylMass
open ContinuousRepresentationScope StandardSMGaugeTensor StandardSMIrreducibility

variable {H G G₀ E E₀ X : Type*} [Group H] [Group G] [Group G₀]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
  (j : SU5.MaximalTorus.Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)
  (j₀ : SU5.MaximalTorus.Torus →* G₀) (rho₀ : Representation ℂ (G₀ × H) E₀)
  (B₀ : SymmetricMass (rho₀.comp (j₀.prodMap (MonoidHom.id H))))
  (D₀ : LightSMAction.Compatible j₀ rho₀ B₀)
  (x : Representation ℂ (GaugeGroup × H) X)
  (e : Representation.Equiv D.action (D₀.action.prod (x.prod x.dual)))
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]

def extension (hx : IsJointlyContinuous x) :
    BalancedSpeciesExtension.Extension j rho B D j₀ rho₀ B₀ D₀ := by
  let : MeasurableSpace GaugeGroup := borel GaugeGroup
  let : BorelSpace GaugeGroup := ⟨rfl⟩
  have hs := CompactIrreducibleQuotient.semisimple (firstRestriction x)
    (hx.comp (ContinuousMonoidHom.inl GaugeGroup H))
  let : IsIrreducible quark := quark_irreducible
  let : IsIrreducible quark.dual := Math.RepresentationTheory.dual_isIrreducible quark
  let : IsIrreducible upRight.dual := upLeft_irreducible
  let : IsIrreducible upRight.dual.dual := Math.RepresentationTheory.dual_isIrreducible upRight.dual
  let : IsIrreducible electronRight.dual := electronLeft_irreducible
  let : IsIrreducible electronRight.dual.dual :=
    Math.RepresentationTheory.dual_isIrreducible electronRight.dual
  exact ⟨VectorlikeMultiplicity.extension x quark D.action D₀.action e hs,
    VectorlikeMultiplicity.extension x upRight.dual D.action D₀.action e hs,
    VectorlikeMultiplicity.extension x electronRight.dual D.action D₀.action e hs⟩

variable (hd : IsJointlyContinuous D.action) (hx : IsJointlyContinuous x)
  {n s : ℕ}
  (hs : ExactSMSpectrum.HasSpectrum (firstRestriction D₀.action) n s) (hn : 0 < n)
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation
    (ResidualWeightSpace.torus (rho₀.comp (j₀.prodMap (MonoidHom.id H)))))
  (c : StructuralConjugation.TwoConjugations j₀)

include e hx hs hn hu c in
theorem shared_positive : SharedPositiveSpeciesIndex.SharedPositive
    (AutomaticSMSpeciesIndex.coefficients j rho B D hd) :=
  BalancedSpeciesExtension.shared_positive j rho B D j₀ rho₀ B₀ D₀ hd
    (extension j rho B D j₀ rho₀ B₀ D₀ x e hx) hs hn hu c

include e hd hx hs hn hu c in
theorem exists_actual_exterior : LightSMSpeciesQque.HasActualExterior j rho B D :=
  BalancedSpeciesQque.exists_actual_exterior j rho B D j₀ rho₀ B₀ D₀ hd
    (extension j rho B D j₀ rho₀ B₀ D₀ x e hx) hs hn hu c

end
end GUT.VectorlikeSpectrumQque
