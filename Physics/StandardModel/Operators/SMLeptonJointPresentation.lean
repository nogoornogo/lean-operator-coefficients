import Math.RepresentationTheory.SU2PairJointPresentation
import Math.RepresentationTheory.SU2SingleJointPresentation
import Physics.StandardModel.Operators.SMLeptonCoreBranching
import Physics.StandardModel.Operators.SMColoredCoreBranching

/-! Actual lepton and conjugate-lepton single-generation cores in the joint
positive support interface. Hypercharge is reattached by its existing
separate neutral-extension theorem. -/
namespace GUT.SMLeptonJointPresentation
set_option autoImplicit false
noncomputable section
open Math Representation JointSourcePresentation SplitRepresentationProjection ExternalInvariantTensor
open scoped TensorProduct

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup
    (WeakDoubletScalars.Doublet ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    (Module.Dual ℂ WeakDoubletScalars.Doublet ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (ℂ ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ ℂ ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance

def lepton (n : ℕ) : Presentation ((SMColoredCoreBranching.core 3).exteriorPower n) :=
  alongEquiv (SMLeptonCoreBranching.exteriorEquiv n) (SU2PairJointPresentation.positive false n)

def conjugateLeptonModel : Representation.Equiv (SMColoredCoreBranching.core 8)
    ((external WeakDoubletScalars.doublet.dual WeakDoubletScalars.doublet).comp
      (SU2PairJointPresentation.projection true)) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro f s
    simp [SMColoredCoreBranching.core,SMGenerationExhaustion.core,SMGenerationCauchy.inclusion,
      DeltaLOneSignedFields.gauge,DeltaLOneSignedFields.rightHanded,
      StandardSMGaugeTensor.lepton,StandardSMGaugeTensor.twist,StandardSMGaugeTensor.phase,
      Representation.tprod_apply,Representation.dual_apply,WeylIndependentAction.spin,
      SMMixedCompactWeyl.compact,WeylSpinor.left,SL2SymmetricEmbeddings.compactInclusion,
      WeakDoubletScalars.doublet,TauCeti.stdRep,TauCeti.SU2.toGL,StandardSMGaugeTensor.weak,
      external,SU2PairJointPresentation.projection]
    rfl

def conjugateLeptonEquiv : Representation.Equiv (SMColoredCoreBranching.core 8)
    (SU2PairExterior.tensor.comp (SU2PairJointPresentation.projection true)) :=
  conjugateLeptonModel.trans (restrictEquiv
    (externalEquiv SU2DoubletDuality.equivalence.symm (.refl WeakDoubletScalars.doublet))
      (SU2PairJointPresentation.projection true))

def conjugateLepton (n : ℕ) : Presentation ((SMColoredCoreBranching.core 8).exteriorPower n) :=
  alongEquiv (conjugateLeptonEquiv.exteriorPower n) (SU2PairJointPresentation.positive true n)

def electronModel : Representation.Equiv (SMColoredCoreBranching.core 4)
    (WeakDoubletScalars.doublet.comp (SU2SingleJointPresentation.projection true)) where
  toLinearEquiv := TensorProduct.lid ℂ WeakDoubletScalars.Doublet
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro z s
    simp [SMColoredCoreBranching.core,SMGenerationExhaustion.core,SMGenerationCauchy.inclusion,
      DeltaLOneSignedFields.gauge,DeltaLOneSignedFields.rightHanded,
      StandardSMGaugeTensor.electronRight,StandardSMGaugeTensor.twist,StandardSMGaugeTensor.phase,
      Representation.tprod_apply,WeylIndependentAction.spin,SMMixedCompactWeyl.compact,
      WeylSpinor.left,SL2SymmetricEmbeddings.compactInclusion,WeakDoubletScalars.doublet,
      TauCeti.stdRep,TauCeti.SU2.toGL,SU2SingleJointPresentation.projection,JointSourceAtoms.rightProjection]
    rfl

def electron (n : ℕ) : Presentation ((SMColoredCoreBranching.core 4).exteriorPower n) :=
  alongEquiv (electronModel.exteriorPower n) (SU2SingleJointPresentation.positive true n)

def conjugateElectronModel : Representation.Equiv (SMColoredCoreBranching.core 9)
    (WeakDoubletScalars.doublet.comp (SU2SingleJointPresentation.projection false)) where
  toLinearEquiv := (TensorProduct.congr (RestrictedColorDuality.scalarDual (G := JointColorSpinWord.Group)).toLinearEquiv
    (.refl ℂ WeakDoubletScalars.Doublet)).trans (TensorProduct.lid ℂ WeakDoubletScalars.Doublet)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro f s
    simp [SMColoredCoreBranching.core,SMGenerationExhaustion.core,SMGenerationCauchy.inclusion,
      DeltaLOneSignedFields.gauge,DeltaLOneSignedFields.rightHanded,
      StandardSMGaugeTensor.electronRight,StandardSMGaugeTensor.twist,StandardSMGaugeTensor.phase,
      Representation.tprod_apply,Representation.dual_apply,WeylIndependentAction.spin,
      SMMixedCompactWeyl.compact,WeylSpinor.left,SL2SymmetricEmbeddings.compactInclusion,
      WeakDoubletScalars.doublet,TauCeti.stdRep,TauCeti.SU2.toGL,
      SU2SingleJointPresentation.projection,JointSourceAtoms.leftProjection]
    rfl

def conjugateElectron (n : ℕ) : Presentation ((SMColoredCoreBranching.core 9).exteriorPower n) :=
  alongEquiv (conjugateElectronModel.exteriorPower n) (SU2SingleJointPresentation.positive false n)

end
end GUT.SMLeptonJointPresentation
