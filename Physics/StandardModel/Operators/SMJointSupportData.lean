import Physics.StandardModel.Operators.SMCoreSourceData
import Math.RepresentationTheory.JointContentData
import Physics.StandardModel.Operators.SMJointHiggsSupport

/-! Executable content expressions and support transport through the same
actual source. Old dependent presentation projections stay abstract. -/
namespace GUT.SMJointSupportData
set_option autoImplicit false
open Math JointSourceExpression
open scoped TensorProduct

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup (SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    (Module.Dual ℂ (SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((Module.Dual ℂ SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance

abbrev Index (c : DeltaLOneSignedInput.Species → Nat) := JointContentData.Index 9 c

def expressionData (c : DeltaLOneSignedInput.Species → Nat) (m : Nat) (o : Index c) : Expr :=
  .tensor (JointContentData.occupied 9 c SMCoreSourceData.coreData o) (JointSourceData.weak m)

noncomputable def cores (c : DeltaLOneSignedInput.Species → Nat) :
    JointContentPresentation.Cores (SMJointContentSupport.tree c) :=
  JointContentPresentation.indexedCores 9 (SMJointContentSupport.leaves c) SMCoreSourceData.corePresentation

noncomputable def presentation (c : DeltaLOneSignedInput.Species → Nat) (m : Nat)
    (o : GenerationTensorSupport.Choice (SMJointContentSupport.tree c)) :=
  JointSourcePresentation.tensor (JointContentPresentation.occupied _ (cores c) o)
    (SMQJointPresentation.weak m)

def DataSupport (c : DeltaLOneSignedInput.Species → Nat) (m : Nat) : Prop :=
  ∃ o : Index c, JointSourceExpression.Supports (expressionData c m o)

theorem expressionData_eq (c : DeltaLOneSignedInput.Species → Nat) (m : Nat) (o : Index c) :
    expressionData c m o = (presentation c m
      (JointContentData.choiceEquiv 9 (SMJointContentSupport.leaves c) o)).expression := by
  exact congrArg (fun e => Expr.tensor e (JointSourceData.weak m))
    (JointContentData.occupied_eq 9 (SMJointContentSupport.leaves c)
      SMCoreSourceData.corePresentation SMCoreSourceData.coreData (fun _ _ => rfl) o)

theorem dataSupport_presented_iff (c : DeltaLOneSignedInput.Species → Nat) (m : Nat) :
    DataSupport c m ↔ JointContentPresentation.Supports (SMJointContentSupport.tree c)
      (cores c) (SMQJointPresentation.weak m) := by
  constructor
  · rintro ⟨o,h⟩
    rw [expressionData_eq] at h
    exact ⟨JointContentData.choiceEquiv 9 (SMJointContentSupport.leaves c) o,h⟩
  · rintro ⟨o,h⟩
    let e : Index c ≃ GenerationTensorSupport.Choice (SMJointContentSupport.tree c) :=
      JointContentData.choiceEquiv 9 (SMJointContentSupport.leaves c)
    refine ⟨e.symm o, ?_⟩
    rw [expressionData_eq]
    change Supports (presentation c m (e (e.symm o))).expression
    rw [e.apply_symm_apply]
    exact h

/-- Both presentations decompose the same full joint source, so no equality
between their dependent dispatch projections is required. -/
theorem dataSupport_iff (c : DeltaLOneSignedInput.Species → Nat) (m : Nat) :
    DataSupport c m ↔ SMJointContentSupport.Supports c m := by
  rw [dataSupport_presented_iff]
  exact (JointContentPresentation.allowed_iff _ (cores c) (SMQJointPresentation.weak m)).symm.trans
    (JointContentPresentation.allowed_iff _ (SMJointContentSupport.cores c) (SMQJointPresentation.weak m))

theorem witness_to_original (c : DeltaLOneSignedInput.Species → Nat) (m : Nat)
    (o : Index c) (h : JointSourceExpression.Supports (expressionData c m o)) :
    SMJointContentSupport.Supports c m :=
  (dataSupport_iff c m).mp ⟨o,h⟩

def HiggsDataSupport {n : Nat} (p : Fin n → DeltaLOneSignedInput.Species) (h d : Nat) : Prop :=
  ∃ m : Fin (SMContentWeakBound.bound p+1), BoundedHiggsSupport.Admissible h d m.val ∧
    DataSupport (SMIteratedContent.counts p) m.val

theorem higgsDataSupport_iff {n : Nat} (p : Fin n → DeltaLOneSignedInput.Species) (h d : Nat) :
    HiggsDataSupport p h d ↔ SMJointHiggsSupport.HiggsSupport p h d := by
  unfold HiggsDataSupport SMJointHiggsSupport.HiggsSupport
  apply exists_congr
  intro m
  exact and_congr_right (fun _ => dataSupport_iff _ _)

theorem original_ql_iff {k : Nat} [NeZero k] (q l : ZMod k) {n : Nat}
    (p : Fin n → DeltaLOneSignedInput.Species) (h d : Nat) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
    QLFiniteSupport.charge q l p = 0 ∧
      SMContentWeakBound.hypercharge p + 3*((h : Int)-d) = 0 ∧ HiggsDataSupport p h d := by
  rw [higgsDataSupport_iff]
  exact SMJointHiggsSupport.original_ql_iff p q l h d

end GUT.SMJointSupportData
