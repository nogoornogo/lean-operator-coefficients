import Physics.StandardModel.Operators.Support.Quark.SMColoredCoreBranching
import Math.RepresentationTheory.Color.SU3.SU3DoubleSpinExterior

/-! Actual Q/conjugate-Q quadratic branches, preserving weak and both spins.
The middle degrees three through nine are not inferred from this result. -/
namespace Physics.SMQCoreBranching
set_option autoImplicit false
noncomputable section
open Math Representation SMColoredCoreBranching
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup
    ((SU3DoubleSpinSquare.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    (Module.Dual ℂ (SU3DoubleSpinSquare.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance

@[reducible] local instance : AddCommGroup (Sym[ℂ]^2 WeakDoubletScalars.Doublet ⊗[ℂ] Sym[ℂ]^2 WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ SU3DoubleSpinSquare.Color ⊗[ℂ] (Sym[ℂ]^2 WeakDoubletScalars.Doublet ⊗[ℂ] Sym[ℂ]^2 WeakDoubletScalars.Doublet)) := inferInstance
@[reducible] local instance : AddCommGroup (SU3DoubleSpinSquare.Color ⊗[ℂ] (Sym[ℂ]^2 WeakDoubletScalars.Doublet ⊗[ℂ] Sym[ℂ]^2 WeakDoubletScalars.Doublet)) := inferInstance
@[reducible] local instance : AddCommGroup (Sym[ℂ]^2 SU3DoubleSpinSquare.Color ⊗[ℂ] Sym[ℂ]^2 WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Sym[ℂ]^2 (Module.Dual ℂ SU3DoubleSpinSquare.Color) ⊗[ℂ] Sym[ℂ]^2 WeakDoubletScalars.Doublet) := inferInstance

@[reducible] local instance : AddCommGroup
    (Module.Dual ℂ SU3DoubleSpinSquare.Color ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((Module.Dual ℂ SU3DoubleSpinSquare.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance

def projection (right : Bool) : SMGenerationCauchy.Group →* SU3DoubleSpinSquare.Group where
  toFun g := (g.1,(g.2.1,if right then g.2.2.2 else g.2.2.1))
  map_one' := by cases right <;> rfl
  map_mul' _ _ := by cases right <;> rfl

theorem actual_positive : core 0=SU3DoubleSpinSquare.tensor.comp (projection false) := by
  ext g a w s
  simp [core,SMGenerationExhaustion.core,SMGenerationCauchy.inclusion,
    DeltaLOneSignedFields.gauge,DeltaLOneSignedFields.rightHanded,
    StandardSMGaugeTensor.quark,StandardSMGaugeTensor.twist,StandardSMGaugeTensor.phase,
    Representation.tprod_apply,WeylIndependentAction.spin,SMMixedCompactWeyl.compact,
    WeylSpinor.left,SL2SymmetricEmbeddings.compactInclusion,SU3DoubleSpinSquare.tensor,
    SU3DoubleSpinSquare.color,SU3DoubleSpinSquare.weak,SU3DoubleSpinSquare.spin,
    SU3DoubleSpinSquare.weakProjection,SU3DoubleSpinSquare.spinProjection,
    SU3DefiningExterior.rho,SmallSpecialUnitary.defining,WeakDoubletScalars.doublet,
    TauCeti.stdRep,TauCeti.SU2.toGL,StandardSMGaugeTensor.color,StandardSMGaugeTensor.weak,projection]
  rfl

theorem actual_negative : core 5=SU3DoubleSpinExterior.negativeInput.comp (projection true) := by
  ext g phi s
  simp [core,SMGenerationExhaustion.core,SMGenerationCauchy.inclusion,
    DeltaLOneSignedFields.gauge,DeltaLOneSignedFields.rightHanded,
    StandardSMGaugeTensor.quark,StandardSMGaugeTensor.twist,StandardSMGaugeTensor.phase,
    Representation.tprod_apply,WeylIndependentAction.spin,SMMixedCompactWeyl.compact,
    WeylSpinor.left,SL2SymmetricEmbeddings.compactInclusion,SU3DoubleSpinExterior.negativeInput,
    SU3DoubleSpinSquare.color,SU3DoubleSpinSquare.weak,SU3DoubleSpinSquare.spin,
    SU3DoubleSpinSquare.weakProjection,SU3DoubleSpinSquare.spinProjection,
    SU3DefiningExterior.rho,SmallSpecialUnitary.defining,WeakDoubletScalars.doublet,
    TauCeti.stdRep,TauCeti.SU2.toGL,StandardSMGaugeTensor.color,StandardSMGaugeTensor.weak,
    projection,Representation.dual_apply]
  rfl

def positiveEquiv : Representation.Equiv (core 0)
    (SU3DoubleSpinSquare.tensor.comp (projection false)) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := congrArg (fun r => r g) actual_positive

def negativeEquiv : Representation.Equiv (core 5)
    (SU3DoubleSpinSquare.dualTensor.comp (projection true)) :=
  ({ toLinearEquiv := .refl ℂ _,isIntertwining' g := congrArg (fun r => r g) actual_negative } :
    Representation.Equiv (core 5) (SU3DoubleSpinExterior.negativeInput.comp (projection true))).trans
      (SplitRepresentationProjection.restrictEquiv SU3DoubleSpinExterior.negativeInputEquiv (projection true))

def positiveSquare : Representation.Equiv ((core 0).exteriorPower 2)
    (((SU3DoubleSpinSquare.first SU3DoubleSpinSquare.color.dual).prod
      (SU3DoubleSpinSquare.second SU3DoubleSpinSquare.color)).comp (projection false)) where
  toLinearEquiv := SU3DoubleSpinSquare.positive.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change SU3DoubleSpinSquare.positive (exteriorPower.map 2 (core 0 g) x)=_
    rw [congrArg (fun r => r g) actual_positive]
    exact SU3DoubleSpinSquare.positive.isIntertwining _ _ (projection false g) x

def negativeSquare : Representation.Equiv ((core 5).exteriorPower 2)
    (((SU3DoubleSpinSquare.first SU3DoubleSpinSquare.color).prod
      (SU3DoubleSpinSquare.second SU3DoubleSpinSquare.color.dual)).comp (projection true)) where
  toLinearEquiv := (negativeEquiv.exteriorPower 2).toLinearEquiv.trans
    SU3DoubleSpinSquare.negative.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (negativeEquiv.exteriorPower 2).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinSquare.negative.isIntertwining _ _ (projection true g)
      ((negativeEquiv.exteriorPower 2) x)
    exact (congrArg SU3DoubleSpinSquare.negative h1).trans h2

def positiveTen : Representation.Equiv ((core 0).exteriorPower 10)
    ((((SU3DoubleSpinSquare.first SU3DoubleSpinSquare.color.dual).prod
      (SU3DoubleSpinSquare.second SU3DoubleSpinSquare.color)).dual).comp (projection false)) where
  toLinearEquiv := SU3DoubleSpinExterior.positiveTen.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change SU3DoubleSpinExterior.positiveTen (exteriorPower.map 10 (core 0 g) x)=_
    rw [congrArg (fun r => r g) actual_positive]
    exact SU3DoubleSpinExterior.positiveTen.isIntertwining _ _ (projection false g) x

def negativeTen : Representation.Equiv ((core 5).exteriorPower 10)
    ((((SU3DoubleSpinSquare.first SU3DoubleSpinSquare.color).prod
      (SU3DoubleSpinSquare.second SU3DoubleSpinSquare.color.dual)).dual).comp (projection true)) where
  toLinearEquiv := (negativeEquiv.exteriorPower 10).toLinearEquiv.trans
    SU3DoubleSpinExterior.negativeTen.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (negativeEquiv.exteriorPower 10).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinExterior.negativeTen.isIntertwining _ _ (projection true g)
      ((negativeEquiv.exteriorPower 10) x)
    exact (congrArg SU3DoubleSpinExterior.negativeTen h1).trans h2

end
end Physics.SMQCoreBranching
