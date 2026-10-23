import Physics.StandardModel.Operators.Support.Quark.SMColoredSquarePair
import Physics.StandardModel.Operators.Support.Decomposition.SMGenerationCoefficients
import Physics.StandardModel.Operators.Support.Lepton.SMLowerHiggsSupport
import Math.RepresentationTheory.Exterior.BinaryPatternExterior
import Math.RepresentationTheory.Exterior.GenerationExteriorProjection

/-! Actual all-Higgs support for U^2 conjugate-U^2 and D^2 conjugate-D^2.
The colored branches couple across species; separate core singlets are not
required. Three generations, independent spins and cyclic q/l are retained. -/
namespace Physics.SMColoredPairHiggsSupport
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance

abbrev pattern (s t : DeltaLOneSignedInput.Species) := BinaryPatternExterior.pattern s t 2 2

def Pairs (s t : DeltaLOneSignedInput.Species) : Prop := (s=1 ∧ t=6) ∨ (s=2 ∧ t=7)

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

abbrev field (s : DeltaLOneSignedInput.Species) : Representation ℂ SMGenerationCauchy.Group
    (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) :=
  (SMCombinedCompactAction.field s).comp SMGenerationCauchy.inclusion
abbrev source (s t : DeltaLOneSignedInput.Species) : Representation ℂ SMGenerationCauchy.Group
    (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) (pattern s t)) :=
  (SMCombinedCompactAction.source flavor (pattern s t)).comp SMGenerationCauchy.inclusion

def sourceEquiv (s t : DeltaLOneSignedInput.Species) (hst : s≠t) : Representation.Equiv
    (((field s).exteriorPower 2).tprod
      ((field t).exteriorPower 2))
    ((SMCombinedCompactAction.source flavor (pattern s t)).comp SMGenerationCauchy.inclusion) :=
  SplitRepresentationProjection.restrictEquiv
    (BinaryPatternExterior.equiv SMCombinedCompactAction.field s t 2 2 hst) SMGenerationCauchy.inclusion

theorem semisimple_source (s t : DeltaLOneSignedInput.Species) (hs : s=1 ∨ s=2)
    (ht : t=6 ∨ t=7) : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((SMCombinedCompactAction.source flavor (pattern s t)).comp SMGenerationCauchy.inclusion)) := by
  have hc := SMColoredSquarePair.allowed s t hs ht
  have hg := GenerationExteriorProjection.tensor_allowed (SMColoredCoreBranching.core s)
    (SMColoredCoreBranching.core t) 2 2 hc
  have hst : s≠t := by rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> decide
  exact (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (sourceEquiv flavor s t hst))).mp hg

def zeroBosonEquiv (s t : DeltaLOneSignedInput.Species) : Representation.Equiv
    ((source flavor s t).tprod (SMGenerationCauchy.weak.symmetricPower 0))
    ((SMCombinedCompactAction.source flavor (pattern s t)).comp SMGenerationCauchy.inclusion) :=
  (ExternalInvariantTensor.tensorEquiv (.refl _)
    (SymmetricPowerLowDegree.representationZeroEquiv SMGenerationCauchy.weak)).trans
    { toLinearEquiv := TensorProduct.rid ℂ _
      isIntertwining' g := by
        apply TensorProduct.ext'
        intro x z
        change z • source flavor s t g x = source flavor s t g (z • x)
        exact (map_smul _ z x).symm }

theorem hypercharge (s t : DeltaLOneSignedInput.Species) (hs : Pairs s t) :
    SMContentWeakBound.hypercharge (pattern s t)=0 := by
  unfold SMContentWeakBound.hypercharge
  rw [Fin.sum_univ_add (a := 2) (b := 2)]
  simp only [pattern,BinaryPatternExterior.pattern,Fin.append_left,Fin.append_right]
  rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [DeltaLOneSignedInput.hypercharge]

theorem local_allowed (s t : DeltaLOneSignedInput.Species) (hs : Pairs s t) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern s t) 0 0)) := by
  have h1 : s=1 ∨ s=2 := by rcases hs with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> simp
  have h2 : t=6 ∨ t=7 := by rcases hs with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp
  have hsource := semisimple_source flavor s t h1 h2
  have hb := (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (zeroBosonEquiv flavor s t))).mpr hsource
  have hr := (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (SMGenerationCoefficients.actionEquiv flavor (pattern s t) 0 0))).mp hb
  have hc : SMContentWeakBound.hypercharge (pattern s t)+3*(0 : ℤ)=0 := by rw [hypercharge s t hs]; rfl
  have hf := SMCombinedChargeSupport.allowed flavor (pattern s t) 0 0 hc hr
  exact (SelectionCriteria.allowed_equiv
    ((SMCombinedCompactAction.coefficientEquiv flavor (pattern s t) 0 0).trans
      (SMMixedCompactCoefficients.localEquiv flavor (pattern s t) 0 0).symm)).mp hf

theorem local_iff (s t : DeltaLOneSignedInput.Species) (hs : Pairs s t) (h d : ℕ) :
    SMLowerHiggsSupport.LocalHiggs flavor (pattern s t) h d ↔ h=d := by
  constructor
  · rintro ⟨m,_,ha⟩
    have hc := SMChargedKernelRank.local_charge flavor (pattern s t) m.val ((h : ℤ)-d) ha
    rw [hypercharge s t hs] at hc
    omega
  · intro hd
    subst d
    refine ⟨⟨0,by omega⟩,?_,?_⟩
    · dsimp [BoundedHiggsSupport.Admissible]
      omega
    · rw [sub_self]
      exact local_allowed flavor s t hs

variable {k : ℕ} [NeZero k] (q l : ZMod k)

omit flavor [NeZero k] in
theorem residual (s t : DeltaLOneSignedInput.Species) (hs : Pairs s t) :
    QLFiniteSupport.charge q l (pattern s t)=0 := by
  unfold QLFiniteSupport.charge
  rw [Fin.sum_univ_add (a := 2) (b := 2)]
  simp only [pattern,BinaryPatternExterior.pattern,Fin.append_left,Fin.append_right]
  rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [DuqlHiggsContent.signedCharge]

omit flavor in
theorem original_ql_iff (s t : DeltaLOneSignedInput.Species) (hs : Pairs s t) (h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor q l) (pattern s t) h d) ↔ h=d := by
  rw [SMLowerHiggsSupport.ql_original_iff,residual q l s t hs,local_iff _ s t hs h d]
  simp

end
end Physics.SMColoredPairHiggsSupport
