import Math.RepresentationTheory.Color.SU3.SU3SpinExterior
import Math.RepresentationTheory.Color.SU3.SU3ConjugateSpinExterior
import Physics.StandardModel.Operators.Support.Decomposition.SMGenerationExhaustion
import Physics.StandardModel.Operators.Support.Decomposition.SMGenerationCauchy

/-! Actual U/D and conjugate-U/D core square branches, with independent
spins retained. Hypercharge and residual phases are separated only by the
existing semisimple restriction, never discarded in coefficient consumers. -/
namespace Physics.SMColoredCoreBranching
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance

def projection (right : Bool) : SMGenerationCauchy.Group →* SU3SpinExterior.Group where
  toFun g := (g.1,if right then g.2.2.2 else g.2.2.1)
  map_one' := by cases right <;> rfl
  map_mul' _ _ := by cases right <;> rfl

theorem projection_surjective (right : Bool) : Function.Surjective (projection right) := by
  intro g
  cases right
  · exact ⟨(g.1,(1,(g.2,1))),rfl⟩
  · exact ⟨(g.1,(1,(1,g.2))),rfl⟩

abbrev core (s : DeltaLOneSignedInput.Species) : Representation ℂ SMGenerationCauchy.Group (SMGenerationExhaustion.Core s) :=
  (SMGenerationExhaustion.core s).comp SMGenerationCauchy.inclusion

theorem actual_up : core 1=SU3SpinExterior.tensor.comp (projection true) := by
  ext g c w
  simp [core,SMGenerationExhaustion.core,SMGenerationCauchy.inclusion,
    DeltaLOneSignedFields.gauge,DeltaLOneSignedFields.rightHanded,
    StandardSMGaugeTensor.upRight,
    StandardSMGaugeTensor.twist,StandardSMGaugeTensor.phase,
    Representation.tprod_apply,WeylIndependentAction.spin,SMMixedCompactWeyl.compact,
    WeylSpinor.left,SL2SymmetricEmbeddings.compactInclusion,SU3SpinExterior.tensor,
    SU3SpinExterior.color,SU3SpinExterior.spin,SU3DefiningExterior.rho,
    SmallSpecialUnitary.defining,WeakDoubletScalars.doublet,TauCeti.stdRep,
    TauCeti.SU2.toGL,StandardSMGaugeTensor.color,projection]
  rfl

theorem actual_down : core 2=SU3SpinExterior.tensor.comp (projection true) := by
  ext g c w
  simp [core,SMGenerationExhaustion.core,SMGenerationCauchy.inclusion,
    DeltaLOneSignedFields.gauge,DeltaLOneSignedFields.rightHanded,
    StandardSMGaugeTensor.downRight,
    StandardSMGaugeTensor.twist,StandardSMGaugeTensor.phase,
    Representation.tprod_apply,WeylIndependentAction.spin,SMMixedCompactWeyl.compact,
    WeylSpinor.left,SL2SymmetricEmbeddings.compactInclusion,SU3SpinExterior.tensor,
    SU3SpinExterior.color,SU3SpinExterior.spin,SU3DefiningExterior.rho,
    SmallSpecialUnitary.defining,WeakDoubletScalars.doublet,TauCeti.stdRep,
    TauCeti.SU2.toGL,StandardSMGaugeTensor.color,projection]
  rfl

theorem actual_conjugateUp : core 6=SU3ConjugateSpinExterior.tensor.comp (projection false) := by
  ext g c w
  simp [core,SMGenerationExhaustion.core,SMGenerationCauchy.inclusion,
    DeltaLOneSignedFields.gauge,DeltaLOneSignedFields.rightHanded,
    StandardSMGaugeTensor.upRight,
    StandardSMGaugeTensor.twist,StandardSMGaugeTensor.phase,
    Representation.tprod_apply,WeylIndependentAction.spin,SMMixedCompactWeyl.compact,
    WeylSpinor.left,SL2SymmetricEmbeddings.compactInclusion,SU3ConjugateSpinExterior.tensor,
    SU3ConjugateSpinExterior.color,SU3ConjugateSpinExterior.spin,SU3DualExterior.rho,
    SU3DefiningExterior.rho,SmallSpecialUnitary.defining,WeakDoubletScalars.doublet,
    TauCeti.stdRep,TauCeti.SU2.toGL,StandardSMGaugeTensor.color,projection,
    Representation.dual_apply]
  rfl

theorem actual_conjugateDown : core 7=SU3ConjugateSpinExterior.tensor.comp (projection false) := by
  ext g c w
  simp [core,SMGenerationExhaustion.core,SMGenerationCauchy.inclusion,
    DeltaLOneSignedFields.gauge,DeltaLOneSignedFields.rightHanded,
    StandardSMGaugeTensor.downRight,
    StandardSMGaugeTensor.twist,StandardSMGaugeTensor.phase,
    Representation.tprod_apply,WeylIndependentAction.spin,SMMixedCompactWeyl.compact,
    WeylSpinor.left,SL2SymmetricEmbeddings.compactInclusion,SU3ConjugateSpinExterior.tensor,
    SU3ConjugateSpinExterior.color,SU3ConjugateSpinExterior.spin,SU3DualExterior.rho,
    SU3DefiningExterior.rho,SmallSpecialUnitary.defining,WeakDoubletScalars.doublet,
    TauCeti.stdRep,TauCeti.SU2.toGL,StandardSMGaugeTensor.color,projection,
    Representation.dual_apply]
  rfl

def positiveEquiv (s : DeltaLOneSignedInput.Species) (hs : s=1 ∨ s=2) :
    Representation.Equiv (core s) (SU3SpinExterior.tensor.comp (projection true)) := by
  by_cases h : s=1
  · subst s
    exact { toLinearEquiv := .refl ℂ _, isIntertwining' g := congrArg (fun r => r g) actual_up }
  · have hh : s=2 := hs.resolve_left h
    subst s
    exact { toLinearEquiv := .refl ℂ _, isIntertwining' g := congrArg (fun r => r g) actual_down }

def negativeEquiv (s : DeltaLOneSignedInput.Species) (hs : s=6 ∨ s=7) :
    Representation.Equiv (core s) (SU3ConjugateSpinExterior.tensor.comp (projection false)) := by
  by_cases h : s=6
  · subst s
    exact { toLinearEquiv := .refl ℂ _, isIntertwining' g := congrArg (fun r => r g) actual_conjugateUp }
  · have hh : s=7 := hs.resolve_left h
    subst s
    exact { toLinearEquiv := .refl ℂ _, isIntertwining' g := congrArg (fun r => r g) actual_conjugateDown }

def positiveExteriorEquiv (s : DeltaLOneSignedInput.Species) (hs : s=1 ∨ s=2) (n : ℕ) :
    Representation.Equiv ((core s).exteriorPower n)
      ((SU3SpinExterior.tensor.exteriorPower n).comp (projection true)) :=
  (positiveEquiv s hs).exteriorPower n

def negativeExteriorEquiv (s : DeltaLOneSignedInput.Species) (hs : s=6 ∨ s=7) (n : ℕ) :
    Representation.Equiv ((core s).exteriorPower n)
      ((SU3ConjugateSpinExterior.tensor.exteriorPower n).comp (projection false)) :=
  (negativeEquiv s hs).exteriorPower n

def positiveSquare (s : DeltaLOneSignedInput.Species) (hs : s=1 ∨ s=2) :
    Representation.Equiv ((core s).exteriorPower 2)
      ((SU3SpinExterior.firstBranch.prod SU3SpinExterior.secondBranch).comp (projection true)) :=
  (positiveExteriorEquiv s hs 2).trans
    (SplitRepresentationProjection.restrictEquiv SU3SpinExterior.squareEquiv (projection true))

def negativeSquare (s : DeltaLOneSignedInput.Species) (hs : s=6 ∨ s=7) :
    Representation.Equiv ((core s).exteriorPower 2)
      ((SU3ConjugateSpinExterior.firstBranch.prod SU3ConjugateSpinExterior.secondBranch).comp (projection false)) :=
  (negativeExteriorEquiv s hs 2).trans
    (SplitRepresentationProjection.restrictEquiv SU3ConjugateSpinExterior.squareEquiv (projection false))

def positiveFour (s : DeltaLOneSignedInput.Species) (hs : s=1 ∨ s=2) :
    Representation.Equiv ((core s).exteriorPower 4)
      ((SU3SpinExterior.firstBranch.prod SU3SpinExterior.secondBranch).dual.comp (projection true)) :=
  (positiveExteriorEquiv s hs 4).trans
    (SplitRepresentationProjection.restrictEquiv SU3SpinExterior.fourEquiv (projection true))

def negativeFour (s : DeltaLOneSignedInput.Species) (hs : s=6 ∨ s=7) :
    Representation.Equiv ((core s).exteriorPower 4)
      ((SU3ConjugateSpinExterior.firstBranch.prod SU3ConjugateSpinExterior.secondBranch).dual.comp (projection false)) :=
  (negativeExteriorEquiv s hs 4).trans
    (SplitRepresentationProjection.restrictEquiv SU3ConjugateSpinExterior.fourEquiv (projection false))

end
end Physics.SMColoredCoreBranching
