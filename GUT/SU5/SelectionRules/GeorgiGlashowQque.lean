import GUT.SU5.SelectionRules.GeorgiGlashowSource
import Physics.StandardModel.Spectrum.ExactSMAutomaticPositive
import Physics.StandardModel.Operators.AutomaticSpeciesQque

open Math

/-! The retained SU(5) matter supplies the positive-constituent test and
therefore the actual nonzero exterior qque coefficient. -/

namespace GUT.SU5.GeorgiGlashowQque
set_option autoImplicit false
noncomputable section
open MatterSource GeorgiGlashowSource StandardModelEmbedding

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  {n : ℕ} (R : OrdinaryAction H n) (hR : Continuous R)

theorem shared_positive (hn : 0 < n) :
    SharedPositiveSpeciesIndex.SharedPositive
      (AutomaticSMSpeciesIndex.coefficients MaximalTorus.hom (joint R) (mass R)
        (compatible R) (compatible_continuous R hR)) :=
  ExactSMAutomaticPositive.shared_positive _ _ _ _ _ (hasSpectrum R) hn
    (torus_unitary R)
    (StandardChainConjugation.threeConjugations (MonoidHom.id TargetGroup)).toTwo

theorem pairwise_positive (hn : 0 < n) :
    AutomaticSMSpeciesIndex.PairwisePositive MaximalTorus.hom (joint R) (mass R)
      (compatible R) (compatible_continuous R hR) :=
  PairwisePositiveSpeciesIndex.of_shared (shared_positive R hR hn)

include hR in
theorem exists_actual_alternation (hn : 0 < n) :
    ∃ fields : LightSMFieldExtraction.Fields (compatible R).action,
      QqueSpinorExterior.HasNonzeroAlternation fields.Q.toRepresentation
        fields.U.toRepresentation fields.E.toRepresentation :=
  AutomaticSpeciesQque.exists_actual_alternation _ _ _ _ _ (pairwise_positive R hR hn)

include hR in
theorem exists_actual_exterior (hn : 0 < n) :
    LightSMSpeciesQque.HasActualExterior MaximalTorus.hom (joint R) (mass R) (compatible R) :=
  AutomaticSpeciesQque.exists_actual_exterior _ _ _ _ _ (pairwise_positive R hR hn)

end
end GUT.SU5.GeorgiGlashowQque

namespace GUT.SU5.GeorgiGlashowBenchmark
noncomputable section
open MatterSource GeorgiGlashowSource ProductFactorization StandardSMGaugeTensor

def trivialAction (n : ℕ) : OrdinaryAction PUnit n := 1

theorem trivialAction_continuous (n : ℕ) : Continuous (trivialAction n) := continuous_const

theorem species_counts (n : ℕ) :
    Module.finrank ℂ (Representation.IntertwiningMap quark
      (firstRestriction (compatible (trivialAction n)).action)) = n ∧
    Module.finrank ℂ (Representation.IntertwiningMap upRight.dual
      (firstRestriction (compatible (trivialAction n)).action)) = n ∧
    Module.finrank ℂ (Representation.IntertwiningMap electronRight.dual
      (firstRestriction (compatible (trivialAction n)).action)) = n :=
  ExactSMSpectrum.exact_species_multiplicities (hasSpectrum (trivialAction n))

theorem one_generation_exterior :
    LightSMSpeciesQque.HasActualExterior MaximalTorus.hom (joint (trivialAction 1))
      (mass (trivialAction 1)) (compatible (trivialAction 1)) :=
  GeorgiGlashowQque.exists_actual_exterior _ (trivialAction_continuous 1) (by decide)

theorem three_generation_exterior :
    LightSMSpeciesQque.HasActualExterior MaximalTorus.hom (joint (trivialAction 3))
      (mass (trivialAction 3)) (compatible (trivialAction 3)) :=
  GeorgiGlashowQque.exists_actual_exterior _ (trivialAction_continuous 3) (by decide)

end
end GUT.SU5.GeorgiGlashowBenchmark
