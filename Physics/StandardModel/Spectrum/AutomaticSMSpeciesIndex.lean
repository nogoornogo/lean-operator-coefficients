import Physics.StandardModel.Spectrum.ExactSMResidualSpectrum
import Physics.StandardModel.Spectrum.PairwisePositiveSpeciesIndex
import Math.RepresentationTheory.Multiplicity.CompactMultiplicityPresentation

open Math

/-! Actual species indices have a normalized finite irreducible presentation.
No exact-spectrum assumption or supplied target family is used here. -/

namespace GUT.AutomaticSMSpeciesIndex
noncomputable section
open Representation InvariantWeylMass ContinuousRepresentationScope ProductFactorization
open SU5.MaximalTorus

variable {H G E : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  (hd : IsJointlyContinuous D.action)

def presentation := CompactMultiplicityPresentation.normalized D.action ExactSMResidualSpectrum.gauge
  (hd.comp (ContinuousMonoidHom.inr _ H))
abbrev Index := (presentation j rho B D hd).Index
abbrev Carrier := (presentation j rho B D hd).Carrier
abbrev action := (presentation j rho B D hd).action
abbrev coefficients := (presentation j rho B D hd).coefficients

theorem continuous (i : Index j rho B D hd) :
    IsJointlyContinuous (action j rho B D hd i) :=
  (presentation j rho B D hd).continuous i

theorem inequivalent (i k : Index j rho B D hd) (hne : i ≠ k) :
    IsEmpty (Representation.Equiv (action j rho B D hd i) (action j rho B D hd k)) :=
  (presentation j rho B D hd).inequivalent i k hne

theorem index_character (s : Fin 5) (h : H) :
    CompactMultiplicityIndex.index D.action (ExactSMResidualSpectrum.gauge s) h =
      CompactVirtualCharacter.character (action j rho B D hd)
        (coefficients j rho B D hd s) h :=
  (presentation j rho B D hd).character s h

theorem species_matches : VirtualSMSpeciesIndex.SpeciesMatches j rho B D
    (action j rho B D hd) (coefficients j rho B D hd) :=
  ⟨index_character j rho B D hd 0,
    index_character j rho B D hd 1,
    index_character j rho B D hd 4⟩

def PairwisePositive : Prop :=
  PairwisePositiveSpeciesIndex.PairwisePositive (coefficients j rho B D hd)

end
end GUT.AutomaticSMSpeciesIndex
