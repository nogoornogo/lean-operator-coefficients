import Physics.StandardModel.Operators.Support.Joint.SMCombinedCompactAction
import Math.RepresentationTheory.SU2.SU2ExteriorBlocks
import Math.RepresentationTheory.Exterior.GenerationExteriorBlocks
import Math.LinearAlgebra.Tensor.TensorDeterminant

/-! Actual color, weak and independent spin actions for the Q/L generation blocks.
Hypercharge is restricted to one here and must be reattached in coefficient consumers. -/
namespace Physics.SMGenerationCauchy
set_option autoImplicit false
noncomputable section
-- Consumers use the proved Cauchy identities and injectivity, never the
-- underlying symmetrization sums at concrete exterior degrees.
attribute [local irreducible] Math.TopExteriorCauchy.map Math.SymmetricCauchy.map
open Math Representation WeakDoubletScalars
open scoped TensorProduct

@[reducible] local instance : AddCommGroup (SMEpsilonTensor.Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((SMEpsilonTensor.Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Doublet ⊗[ℂ] Doublet) := inferInstance

abbrev Group := Matrix.specialUnitaryGroup (Fin 3) ℂ ×
  (TauCeti.SU2 × (TauCeti.SU2 × TauCeti.SU2))
def inclusion : Group →* SMCombinedCompactAction.Group where
  toFun g := ((g.1,(g.2.1,1)),g.2.2)
  map_one' := rfl
  map_mul' _ _ := by simp

def weakProjection : Group →* TauCeti.SU2 :=
  (MonoidHom.fst _ _).comp (MonoidHom.snd _ _)
def spinProjection : Group →* TauCeti.SU2 :=
  (MonoidHom.fst _ _).comp ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _))
abbrev color : Representation ℂ Group SMEpsilonTensor.Color := StandardSMGaugeTensor.color.comp
  ((MonoidHom.fst _ _).comp inclusion)
abbrev weak : Representation ℂ Group Doublet := doublet.comp weakProjection
abbrev spin : Representation ℂ Group Doublet := doublet.comp spinProjection
abbrev quark : Representation ℂ Group ((SMEpsilonTensor.Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) :=
  (color.tprod weak).tprod spin
abbrev lepton : Representation ℂ Group (Doublet ⊗[ℂ] Doublet) := weak.tprod spin
abbrev generations {V : Type*} [AddCommGroup V] [Module ℂ V] (r : Representation ℂ Group V) :=
  r.tprod (Representation.trivial ℂ Group (Fin 3 → ℂ))

theorem color_det (g : Group) : LinearMap.det (color g) = 1 := by
  change LinearMap.det (Matrix.toLin' (g.1 : Matrix (Fin 3) (Fin 3) ℂ)) = 1
  rw [LinearMap.det_toLin']
  exact g.1.prop.2

theorem spin_det (g : Group) : LinearMap.det (spin g) = 1 := by
  change LinearMap.det (Matrix.toLin' (g.2.2.1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1
  rw [LinearMap.det_toLin']
  exact g.2.2.1.prop.2

def colorBasis := Pi.basisFun ℂ (Fin 3)
def spinBasis := Pi.basisFun ℂ (Fin 2)
def sixBasis : Module.Basis (Fin 6) ℂ (SMEpsilonTensor.Color ⊗[ℂ] Doublet) :=
  (colorBasis.tensorProduct spinBasis).reindex finProdFinEquiv

theorem color_spin_det (g : Group) : LinearMap.det ((color.tprod spin) g) = 1 :=
  TensorDeterminant.map_one colorBasis spinBasis (color g) (spin g) (color_det g) (spin_det g)

def reorder : Representation.Equiv ((color.tprod spin).tprod weak) quark :=
  (Representation.TensorProduct.assoc color spin weak).trans
    ((ExternalInvariantTensor.tensorEquiv (.refl color)
      (Representation.TensorProduct.comm spin weak)).trans
        (Representation.TensorProduct.assoc color weak spin).symm)

def quarkSix : IntertwiningMap (weak.symmetricPower 6) (quark.exteriorPower 6) :=
  (reorder.exteriorPower 6).toIntertwiningMap.comp
    (TopExteriorCauchy.intertwiner sixBasis (color.tprod spin) weak color_spin_det)

theorem quarkSix_injective : Function.Injective (fun x : Sym[ℂ]^6 Doublet => quarkSix x) :=
by
  intro x y h
  apply SU2ExteriorBlocks.column_injective sixBasis
  apply (reorder.exteriorPower 6).injective
  exact h

def quarkThree : IntertwiningMap ((weak.symmetricPower 3).tprod (spin.symmetricPower 3))
    (quark.exteriorPower 3) :=
  ((Representation.TensorProduct.assoc color weak spin).symm.exteriorPower 3).toIntertwiningMap.comp
    (ExtremeCauchyBlocks.rowColumn colorBasis color weak spin color_det)

theorem quarkThree_injective : Function.Injective quarkThree :=
  ((Representation.TensorProduct.assoc color weak spin).symm.exteriorPower 3).injective.comp
    (SU2ExteriorBlocks.rowColumn_injective colorBasis)

def leptonTwo : IntertwiningMap (weak.symmetricPower 2) (lepton.exteriorPower 2) :=
  ((Representation.TensorProduct.comm spin weak).exteriorPower 2).toIntertwiningMap.comp
    (TopExteriorCauchy.intertwiner spinBasis spin weak spin_det)

theorem leptonTwo_injective : Function.Injective leptonTwo :=
  ((Representation.TensorProduct.comm spin weak).exteriorPower 2).injective.comp
    (SU2ExteriorBlocks.column_injective spinBasis)

def leptonOne : Representation.Equiv ((weak.symmetricPower 1).tprod (spin.symmetricPower 1))
    (lepton.exteriorPower 1) :=
  (ExternalInvariantTensor.tensorEquiv (SymmetricPowerLowDegree.representationOneEquiv weak)
    (SymmetricPowerLowDegree.representationOneEquiv spin)).trans lepton.exteriorPowerOneEquiv.symm

theorem actual_quark : (SMCombinedCompactAction.field 0).comp inclusion = generations quark := by
  ext g a w s f
  simp [SMCombinedCompactAction.field, inclusion, DeltaLOneSignedFields.gauge,
    DeltaLOneSignedFields.rightHanded, StandardSMGaugeTensor.quark, StandardSMGaugeTensor.twist,
    StandardSMGaugeTensor.phase, Representation.tprod_apply,
    WeylIndependentAction.spin, SMMixedCompactWeyl.compact, WeylSpinor.left,
    SL2SymmetricEmbeddings.compactInclusion, generations, quark, color, weak, spin,
    weakProjection, spinProjection, WeakDoubletScalars.doublet, TauCeti.stdRep, TauCeti.SU2.toGL,
    StandardSMGaugeTensor.weak]
  rfl

theorem actual_lepton : (SMCombinedCompactAction.field 3).comp inclusion = generations lepton := by
  ext g w s f
  simp [SMCombinedCompactAction.field, inclusion, DeltaLOneSignedFields.gauge,
    DeltaLOneSignedFields.rightHanded, StandardSMGaugeTensor.lepton, StandardSMGaugeTensor.twist,
    StandardSMGaugeTensor.phase, Representation.tprod_apply,
    WeylIndependentAction.spin, SMMixedCompactWeyl.compact, WeylSpinor.left,
    SL2SymmetricEmbeddings.compactInclusion, generations, lepton, weak, spin,
    weakProjection, spinProjection, WeakDoubletScalars.doublet, TauCeti.stdRep, TauCeti.SU2.toGL,
    StandardSMGaugeTensor.weak]
  rfl

end
end Physics.SMGenerationCauchy
