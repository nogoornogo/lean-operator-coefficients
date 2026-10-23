import Math.LieGroups.SpecialUnitary.Block
import GUT.Common.StandardChain.StandardChain

open Physics

open Math

/-! The common selection-rule theorem along the standard SU(5) block in
SU(5+k). The exact dual light target remains an explicit model input. -/

set_option autoImplicit false

namespace GUT.SUN.StandardChain
open Math.SUN


noncomputable section

open FiniteAbelianChargeSectors InvariantWeylMass SU5

abbrev inclusion (k : ℕ) := Block.inclusion 5 k

variable {H E : Type*} [CommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

abbrev Model (k : ℕ) (rho : Representation ℂ (Block.Group (5 + k) × H) E) :=
  GUT.StandardChain.Model (inclusion k) rho

theorem selection_rule_obstruction {k : ℕ}
    {rho : Representation ℂ (Block.Group (5 + k) × H) E} (M : Model k rho) :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      M.lightSpectrum := M.selection_rule_obstruction

def continuousModel [TopologicalSpace H] [IsTopologicalGroup H] {k : ℕ}
    {rho : Representation ℂ (Block.Group (5 + k) × H) E} (M : Model k rho)
    (hc : Continuous (fun p : (Block.Group (5 + k) × H) × E => rho p.1 p.2)) :
    GUT.StandardChain.ContinuousModel (inclusion k) rho where
  toModel := M
  inclusion_injective := Block.inclusion_injective 5 k
  inclusion_continuous := Block.inclusion_continuous 5 k
  action_continuous := hc

theorem rank_five_inclusion : inclusion 0 = MonoidHom.id StandardModelEmbedding.TargetGroup :=
  Block.inclusion_zero 5

omit [FiniteDimensional ℂ E] in
theorem rank_five_pullback (rho : Representation ℂ (StandardModelEmbedding.TargetGroup × H) E) :
    GUT.StandardChain.pullback (inclusion 0) rho = rho := by
  rw [rank_five_inclusion]
  rfl

end

end GUT.SUN.StandardChain
