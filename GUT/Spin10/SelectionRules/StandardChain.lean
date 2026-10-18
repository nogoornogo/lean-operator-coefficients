import Math.LieGroups.Spin.SU5Inclusion
import GUT.Common.StandardChain.StandardChain

open Math

/-! The standard-chain supported Abelian selection-rule obstruction in actual
compact Spin(10). The exact light target remains an explicit model input;
the actual half-spin inhabitant is constructed separately in HalfSpinBenchmark. -/

set_option autoImplicit false

namespace GUT.CompactSpin.StandardChain

open Math.CompactSpin
noncomputable section

variable {H E : Type*} [CommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

abbrev Model (rho : Representation ℂ (CompactSpin.Group 10 × H) E) :=
  GUT.StandardChain.Model SU5Inclusion rho

theorem selection_rule_obstruction {rho : Representation ℂ (CompactSpin.Group 10 × H) E}
    (M : Model rho) :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator M.lightSpectrum :=
  M.selection_rule_obstruction

def continuousModel [TopologicalSpace H] [IsTopologicalGroup H]
    {rho : Representation ℂ (CompactSpin.Group 10 × H) E} (M : Model rho)
    (hc : Continuous (fun p : (CompactSpin.Group 10 × H) × E => rho p.1 p.2)) :
    GUT.StandardChain.ContinuousModel SU5Inclusion rho where
  toModel := M
  inclusion_injective := SU5Inclusion_injective
  inclusion_continuous := SU5Inclusion_continuous
  action_continuous := hc

theorem continuous_selection_rule_obstruction [TopologicalSpace H] [IsTopologicalGroup H]
    {rho : Representation ℂ (CompactSpin.Group 10 × H) E}
    (M : GUT.StandardChain.ContinuousModel SU5Inclusion rho) :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      M.toModel.lightSpectrum := M.selection_rule_obstruction

section Scalar

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]

abbrev ScalarModel (rho : Representation ℂ (CompactSpin.Group 10 × H) E)
    (sigma : Representation ℂ (SU5.TorusCharacter.CombinedGroup H) S) :=
  GUT.StandardChain.ScalarModel SU5Inclusion rho sigma

theorem scalar_selection_rule_obstruction
    {rho : Representation ℂ (CompactSpin.Group 10 × H) E}
    {sigma : Representation ℂ (SU5.TorusCharacter.CombinedGroup H) S} (M : ScalarModel rho sigma) :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      M.toMassModel.lightSpectrum := M.selection_rule_obstruction

def scalarContinuousModel [TopologicalSpace H] [IsTopologicalGroup H]
    {rho : Representation ℂ (CompactSpin.Group 10 × H) E}
    {sigma : Representation ℂ (SU5.TorusCharacter.CombinedGroup H) S} (M : ScalarModel rho sigma)
    (hc : Continuous (fun p : (CompactSpin.Group 10 × H) × E => rho p.1 p.2)) :
    GUT.StandardChain.ContinuousModel SU5Inclusion rho :=
  M.toContinuousMassModel SU5Inclusion_injective SU5Inclusion_continuous hc

end Scalar

end

end GUT.CompactSpin.StandardChain
