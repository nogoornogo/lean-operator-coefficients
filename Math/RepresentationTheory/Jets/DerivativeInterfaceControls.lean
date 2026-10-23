import Math.RepresentationTheory.Jets.DerivativeInterface
import Math.RepresentationTheory.Jets.JetAdapterControls

/-! Compiled common-operation usage on the complete mixed two-derivative source. -/
namespace Math.DerivativeInterfaceControls
set_option autoImplicit false
noncomputable section
open Representation MixedJetQuadratic

@[reducible] local instance (d : ℕ) : AddCommGroup (MixedOperatorInput.Source Unit Unit Unit 2 1 d) := inferInstance
@[reducible] local instance (d : ℕ) : Module ℂ (MixedOperatorInput.Source Unit Unit Unit 2 1 d) := inferInstance

abbrev fieldAction : Representation ℂ Unit (JetLinear.Field Unit) := trivial ℂ Unit _
abbrev directionAction : Representation ℂ Unit (JetDirections.Direction Unit) := trivial ℂ Unit _

def mixed := DerivativeInterface.graded fieldAction fieldAction directionAction 2 1 2

theorem mixed_relations : mixed.relations = relations := by
  change CovariantJetIBP.relations
    (V := fun d => MixedOperatorInput.Source Unit Unit Unit 2 1 d)
    (DirectionalJetIBP.mixedDerivatives (F := Unit) (B := Unit) (I := Unit) 2 1) 1 =
    GradedJetIBP.relations (V := fun d => MixedOperatorInput.Source Unit Unit Unit 2 1 d)
      (MixedJetIBP.derivatives (F := Unit) (B := Unit) (I := Unit) 2 1) 1
  exact CovariantJetIBP.relations_eq _ _

theorem mixed_admissible_iff (f : IntertwiningMap mixed.action (trivial ℂ Unit ℂ)) :
    f ∈ mixed.Coefficient ↔ f first + f second = 0 := by
  change mixed.relations ≤ f.toLinearMap.ker ↔ _
  rw [mixed_relations, relations_span, Submodule.span_singleton_le_iff_mem]
  change f (first + second) = 0 ↔ _
  rw [map_add]

/-- The caller uses the same dot-operation as for the EOM model. -/
theorem mixed_extraction (f : mixed.Coefficient) :
    mixed.coefficientEquiv f (mixed.projection first) = f.val first := mixed.extraction f first

end
end Math.DerivativeInterfaceControls
