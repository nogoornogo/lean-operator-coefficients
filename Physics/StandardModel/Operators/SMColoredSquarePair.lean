import Physics.StandardModel.Operators.SMColoredCoreBranching
import Math.RepresentationTheory.SpinSquarePairing

/-! Actual nonzero mixed colored core coefficients, with left and right
spins independent. Hypercharge and residual charges remain separate gates. -/
namespace GUT.SMColoredSquarePair
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance

abbrev color : Representation ℂ SMGenerationCauchy.Group SU3DefiningExterior.Vector :=
  SU3SpinExterior.color.comp (SMColoredCoreBranching.projection true)
abbrev right : Representation ℂ SMGenerationCauchy.Group WeakDoubletScalars.Doublet :=
  SU3SpinExterior.spin.comp (SMColoredCoreBranching.projection true)
abbrev left : Representation ℂ SMGenerationCauchy.Group WeakDoubletScalars.Doublet :=
  SU3SpinExterior.spin.comp (SMColoredCoreBranching.projection false)

def rightTop : Representation.Equiv (right.exteriorPower 2)
    (trivial ℂ SMGenerationCauchy.Group ℂ) :=
  SplitRepresentationProjection.restrictEquiv SU3SpinExterior.spinTop (SMColoredCoreBranching.projection true)

def leftTop : Representation.Equiv (left.exteriorPower 2)
    (trivial ℂ SMGenerationCauchy.Group ℂ) :=
  SplitRepresentationProjection.restrictEquiv SU3SpinExterior.spinTop (SMColoredCoreBranching.projection false)

theorem allowed (s t : DeltaLOneSignedInput.Species) (hs : s=1 ∨ s=2) (ht : t=6 ∨ t=7) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (((SMColoredCoreBranching.core s).exteriorPower 2).tprod
        ((SMColoredCoreBranching.core t).exteriorPower 2))) := by
  have hm := SpinSquarePairing.allowed color right left rightTop leftTop
    (Pi.single (0 : Fin 3) (1 : ℂ)) (LinearMap.proj (0 : Fin 3)) (by simp)
  exact (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (ExternalInvariantTensor.tensorEquiv
      (SMColoredCoreBranching.positiveExteriorEquiv s hs 2)
      (SMColoredCoreBranching.negativeExteriorEquiv t ht 2)))).mpr hm

end
end GUT.SMColoredSquarePair
