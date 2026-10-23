import Physics.StandardModel.Operators.Support.Quark.SMQCoreBranching
import Physics.StandardModel.Operators.Support.Quark.SMColoredPairHiggsSupport
import Math.RepresentationTheory.Tensors.InvariantPairing

/-! Actual all-Higgs Q^2 conjugate-Q^2 support. The full quadratic Q
splitting supplies surjective opposite-color scalar-spin branches. -/
namespace Physics.SMQPairHiggsSupport
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
abbrev color : Representation ℂ SMGenerationCauchy.Group SU3DefiningExterior.Vector :=
  SU3DoubleSpinSquare.color.comp (SMQCoreBranching.projection false)
abbrev pattern := SMColoredPairHiggsSupport.pattern 0 5

def positiveColor : IntertwiningMap ((SMColoredCoreBranching.core 0).exteriorPower 2) color.dual where
  toLinearMap := (LinearMap.snd ℂ _ _).comp
    ((LinearMap.fst ℂ _ _).comp SMQCoreBranching.positiveSquare.toLinearEquiv.toLinearMap)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun y => y.1.2) (SMQCoreBranching.positiveSquare.isIntertwining _ _ g x)

def negativeColor : IntertwiningMap ((SMColoredCoreBranching.core 5).exteriorPower 2) color where
  toLinearMap := (LinearMap.snd ℂ _ _).comp
    ((LinearMap.fst ℂ _ _).comp SMQCoreBranching.negativeSquare.toLinearEquiv.toLinearMap)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun y => y.1.2) (SMQCoreBranching.negativeSquare.isIntertwining _ _ g x)

theorem positiveColor_surjective : Function.Surjective positiveColor := by
  intro z
  refine ⟨SMQCoreBranching.positiveSquare.symm ((0,z),(0,0)),?_⟩
  change (SMQCoreBranching.positiveSquare (SMQCoreBranching.positiveSquare.symm ((0,z),(0,0)))).1.2=z
  rw [Representation.Equiv.apply_symm_apply]

theorem negativeColor_surjective : Function.Surjective negativeColor := by
  intro z
  refine ⟨SMQCoreBranching.negativeSquare.symm ((0,z),(0,0)),?_⟩
  change (SMQCoreBranching.negativeSquare (SMQCoreBranching.negativeSquare.symm ((0,z),(0,0)))).1.2=z
  rw [Representation.Equiv.apply_symm_apply]

def coreCoefficient : InvariantCoefficientTransport.Invariants
    (((SMColoredCoreBranching.core 0).exteriorPower 2).tprod
      ((SMColoredCoreBranching.core 5).exteriorPower 2)) :=
  (InvariantPairing.evaluation color).comp
    ((Representation.TensorProduct.comm color.dual color).toIntertwiningMap.comp
      (positiveColor.tensor negativeColor))

theorem core_allowed : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
    (((SMColoredCoreBranching.core 0).exteriorPower 2).tprod
      ((SMColoredCoreBranching.core 5).exteriorPower 2))) := by
  obtain ⟨x,hx⟩ := positiveColor_surjective (SU3DefiningExterior.basis.coord 0)
  obtain ⟨y,hy⟩ := negativeColor_surjective (SU3DefiningExterior.basis 0)
  refine ⟨coreCoefficient,?_⟩
  intro hz
  have he := DFunLike.congr_fun hz (x ⊗ₜ[ℂ] y)
  change positiveColor x (negativeColor y)=0 at he
  rw [hx,hy] at he
  simp at he

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

theorem semisimple_source : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
    ((SMCombinedCompactAction.source flavor pattern).comp SMGenerationCauchy.inclusion)) := by
  have hg := GenerationExteriorProjection.tensor_allowed (SMColoredCoreBranching.core 0)
    (SMColoredCoreBranching.core 5) 2 2 core_allowed
  exact (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (SMColoredPairHiggsSupport.sourceEquiv flavor 0 5 (by decide)))).mp hg

omit flavor in
theorem hypercharge : SMContentWeakBound.hypercharge pattern=0 := by
  unfold SMContentWeakBound.hypercharge
  rw [Fin.sum_univ_add (a := 2) (b := 2)]
  simp only [pattern,SMColoredPairHiggsSupport.pattern,BinaryPatternExterior.pattern,Fin.append_left,Fin.append_right]
  simp [DeltaLOneSignedInput.hypercharge]

theorem local_allowed : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
    (SMIntegralLocalWeights.action flavor pattern 0 0)) := by
  have hb := (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (SMColoredPairHiggsSupport.zeroBosonEquiv flavor 0 5))).mpr (semisimple_source flavor)
  have hr := (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (SMGenerationCoefficients.actionEquiv flavor pattern 0 0))).mp hb
  have hc : SMContentWeakBound.hypercharge pattern+3*(0 : ℤ)=0 := by rw [hypercharge]; rfl
  have hf := SMCombinedChargeSupport.allowed flavor pattern 0 0 hc hr
  exact (SelectionCriteria.allowed_equiv ((SMCombinedCompactAction.coefficientEquiv flavor pattern 0 0).trans
    (SMMixedCompactCoefficients.localEquiv flavor pattern 0 0).symm)).mp hf

theorem local_iff (h d : ℕ) : SMLowerHiggsSupport.LocalHiggs flavor pattern h d ↔ h=d := by
  constructor
  · rintro ⟨m,_,ha⟩
    have hc := SMChargedKernelRank.local_charge flavor pattern m.val ((h : ℤ)-d) ha
    rw [hypercharge] at hc
    omega
  · intro hd
    subst d
    refine ⟨⟨0,by omega⟩,?_,?_⟩
    · dsimp [BoundedHiggsSupport.Admissible]
      omega
    · rw [sub_self]
      exact local_allowed flavor

variable {k : ℕ} [NeZero k] (q l : ZMod k)

omit flavor [NeZero k] in
theorem residual : QLFiniteSupport.charge q l pattern=0 := by
  unfold QLFiniteSupport.charge
  rw [Fin.sum_univ_add (a := 2) (b := 2)]
  simp only [pattern,SMColoredPairHiggsSupport.pattern,BinaryPatternExterior.pattern,Fin.append_left,Fin.append_right]
  simp [DuqlHiggsContent.signedCharge]

omit flavor in
/-- Actual three-generation Q^2 conjugate-Q^2 permission for every Higgs
bidegree and every existing cyclic scalar q/l action. -/
theorem original_ql_iff (h d : ℕ) : SelectionCriteria.Allowed
    (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) pattern h d) ↔ h=d := by
  rw [SMLowerHiggsSupport.ql_original_iff,residual q l,local_iff _ h d]
  simp

end
end Physics.SMQPairHiggsSupport
