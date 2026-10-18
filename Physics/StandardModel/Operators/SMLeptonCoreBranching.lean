import Math.RepresentationTheory.SU2PairExterior
import Math.RepresentationTheory.SU2PairGenerationSupport
import Math.RepresentationTheory.SU2PairGenerationBounds
import Math.RepresentationTheory.Decomposition.SurjectiveHomTransport
import Physics.StandardModel.Operators.SMGenerationCauchy
import Physics.StandardModel.Operators.SMGenerationExhaustion
import Physics.StandardModel.Operators.SMGenerationCoefficients

/-! Complete joint weak/spin support for the actual single-generation L
core after separating hypercharge. The two independent spin factors remain
in the retained group; neither is silently identified with the other. -/
namespace GUT.SMLeptonCoreBranching
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

@[reducible] local instance (a b : ℕ) : AddCommGroup (SU2PairExterior.PairCarrier a b) := inferInstance
@[reducible] local instance : AddCommGroup
    (WeakDoubletScalars.Doublet ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((WeakDoubletScalars.Doublet ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] (Fin 3 → ℂ)) := inferInstance

def projection : SMGenerationCauchy.Group →* (TauCeti.SU2 × TauCeti.SU2) where
  toFun g := (g.2.1,g.2.2.1)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projection_surjective : Function.Surjective projection :=
  fun g => ⟨(1,(g.1,(g.2,1))),rfl⟩

abbrev core : Representation ℂ SMGenerationCauchy.Group (SMGenerationExhaustion.Core 3) :=
  (SMGenerationExhaustion.core 3).comp SMGenerationCauchy.inclusion

theorem actual_core : (SMGenerationExhaustion.core 3).comp SMGenerationCauchy.inclusion =
    SU2PairExterior.tensor.comp projection := by
  ext g w s
  simp [SMGenerationExhaustion.core,SMGenerationCauchy.inclusion,
    DeltaLOneSignedFields.gauge,DeltaLOneSignedFields.rightHanded,
    StandardSMGaugeTensor.lepton,StandardSMGaugeTensor.twist,StandardSMGaugeTensor.phase,
    Representation.tprod_apply,WeylIndependentAction.spin,SMMixedCompactWeyl.compact,
    WeylSpinor.left,SL2SymmetricEmbeddings.compactInclusion,SU2PairExterior.tensor,
    SU2PairExterior.left,SU2PairExterior.right,SU2ExteriorBlocks.left,SU2ExteriorBlocks.right,
    WeakDoubletScalars.doublet,TauCeti.stdRep,TauCeti.SU2.toGL,StandardSMGaugeTensor.weak,
    projection]
  rfl

def exteriorEquiv (n : ℕ) : Representation.Equiv
    (core.exteriorPower n)
    ((SU2PairExterior.tensor.exteriorPower n).comp projection) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    change exteriorPower.map n (core g) = exteriorPower.map n (SU2PairExterior.tensor (projection g))
    exact congrArg (exteriorPower.map n) (congrArg (fun r => r g) actual_core)

/-- Exact occurrence for every exterior degree and both joint labels. The
actual hypercharge and q/l characters are handled by their separate proved
consumers; this restriction sets hypercharge to one. -/
theorem target_iff (n a b : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap
      (core.exteriorPower n)
      ((SU2PairExterior.pair a b).comp projection)) ↔
      ((n=0 ∨ n=4) ∧ a=0 ∧ b=0) ∨
      ((n=1 ∨ n=3) ∧ a=1 ∧ b=1) ∨
      (n=2 ∧ ((a=2 ∧ b=0) ∨ (a=0 ∧ b=2))) :=
  (SelectionCriteria.allowed_equiv (CompactCoefficientSupport.homEquiv (exteriorEquiv n)
    (.refl ((SU2PairExterior.pair a b).comp projection)))).trans
    ((SelectionCriteria.allowed_equiv (SurjectiveHomTransport.homEquiv projection
      projection_surjective (SU2PairExterior.tensor.exteriorPower n) (SU2PairExterior.pair a b))).trans
      (SU2PairExterior.target_iff n a b))

abbrev field : Representation ℂ SMGenerationCauchy.Group
    (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) 3) :=
  (SMCombinedCompactAction.field 3).comp SMGenerationCauchy.inclusion

theorem actual_field : field=SU2PairGenerationSupport.generations.comp projection := by
  change (SMCombinedCompactAction.field 3).comp SMGenerationCauchy.inclusion=_
  rw [SMGenerationCauchy.actual_lepton]
  ext g w s f
  rfl

def fieldExteriorEquiv (n : ℕ) : Representation.Equiv (field.exteriorPower n)
    ((SU2PairGenerationSupport.generations.exteriorPower n).comp projection) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    change exteriorPower.map n (field g) =
      exteriorPower.map n (SU2PairGenerationSupport.generations (projection g))
    exact congrArg (exteriorPower.map n) (congrArg (fun r => r g) actual_field)

/-- Complete three-generation joint support with only finite occupation
counts, exterior branch choices and triangle/parity conditions remaining.
No Hom, signed coefficient sum or numerical multiplicity remains on the
right. This consumer retains the semisimple group, including unused color
and the independent right spin, exactly as in the actual field action. -/
theorem generation_target_iff (n a b : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap (field.exteriorPower n)
      ((SU2PairExterior.pair a b).comp projection)) ↔
      ∃ i j k, i≤4 ∧ j≤4 ∧ k≤4 ∧ i+(j+k)=n ∧
        SU2PairGenerationSupport.TripleSupport i j k a b :=
  (SelectionCriteria.allowed_equiv (CompactCoefficientSupport.homEquiv (fieldExteriorEquiv n)
    (.refl ((SU2PairExterior.pair a b).comp projection)))).trans
    ((SelectionCriteria.allowed_equiv (SurjectiveHomTransport.homEquiv projection
      projection_surjective (SU2PairGenerationSupport.generations.exteriorPower n)
        (SU2PairExterior.pair a b))).trans (SU2PairGenerationSupport.target_iff n a b))

/-- Closed inequalities and parity, rather than an unevaluated Hom or path
search, for every joint target of the actual three-generation L field. -/
theorem generation_bounds_iff (n a b : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap (field.exteriorPower n)
      ((SU2PairExterior.pair a b).comp projection)) ↔ SU2PairGenerationBounds.Bounds n a b :=
  (generation_target_iff n a b).trans (SU2PairGenerationBounds.paths_iff n a b)

theorem generation_forbidden_iff (n a b : ℕ) :
    SelectionCriteria.Forbidden (IntertwiningMap (field.exteriorPower n)
      ((SU2PairExterior.pair a b).comp projection)) ↔ ¬ SU2PairGenerationBounds.Bounds n a b := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,generation_bounds_iff]

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

/-- Connect the closed joint classification to the actual statistical
constant-L source, retaining the complete semisimple action. -/
theorem source_target_iff (n a b : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap
      ((SMCombinedCompactAction.source flavor (fun _ : Fin n => 3)).comp SMGenerationCauchy.inclusion)
      ((SU2PairExterior.pair a b).comp projection)) ↔ SU2PairGenerationBounds.Bounds n a b :=
  (SelectionCriteria.allowed_equiv (CompactCoefficientSupport.homEquiv
    (SMGenerationCoefficients.sourceEquiv flavor 3 n field rfl).symm
    (.refl ((SU2PairExterior.pair a b).comp projection)))).trans (generation_bounds_iff n a b)

end
end GUT.SMLeptonCoreBranching
