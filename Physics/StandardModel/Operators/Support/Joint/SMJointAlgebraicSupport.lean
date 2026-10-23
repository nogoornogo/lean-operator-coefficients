import Physics.StandardModel.Operators.Support.Joint.SMJointCoefficient
import Physics.StandardModel.Operators.Support.Decomposition.SMComputableCharacter
import Physics.StandardModel.Operators.Support.Quark.SMQLCompactMultiplicity

/-! A uniform algebraic occurrence criterion for actual mixed contents.
All color, weak and independent spin coordinates are retained until the
positive-root differences. No closed multiplicity/rank numeral is proved.
The optional Weyl input remains the existing coefficient-model input. -/
namespace Physics.SMJointAlgebraicSupport
set_option autoImplicit false
open Math Representation SMCompactTorus

/-- Independent weak, left and right root differences at one joint weight. -/
def spinCoefficient (f : Weight → ℤ) (w : Weight) : ℤ :=
  f w - f (w+weakRoot) - f (w+leftRoot) - f (w+rightRoot) +
    f (w+weakRoot+leftRoot) + f (w+weakRoot+rightRoot) +
    f (w+leftRoot+rightRoot) - f (w+weakRoot+leftRoot+rightRoot)

/-- The six color terms, each retaining all three SU2 differences. -/
def balance (f : Weight → ℤ) : ℤ :=
  spinCoefficient f 0 - spinCoefficient f alpha - spinCoefficient f beta +
    spinCoefficient f (alpha+alpha+beta) + spinCoefficient f (alpha+beta+beta) -
    spinCoefficient f (alpha+alpha+beta+beta)

theorem spin_formula (f : Weight → ℤ) (w : Weight) :
    CompactWeylExtraction.extractAt [weakRoot,leftRoot,rightRoot] f w =
      spinCoefficient f w := by
  simp only [CompactWeylExtraction.extractAt,CompactWeylExtraction.difference,spinCoefficient]
  abel

theorem root_formula (f : Weight → ℤ) :
    CompactWeylExtraction.constantTerm roots f = balance f := by
  change CompactWeylExtraction.constantTerm [alpha,beta,alpha+beta]
    (CompactWeylExtraction.extractAt [weakRoot,leftRoot,rightRoot] f) = _
  rw [CompactWeylExtraction.a2_formula]
  simp only [spin_formula,balance]

theorem terms_balance (t : ComputableWeightPolynomial.Terms Weight) :
    CompactWeylExtraction.constantTerm roots (ComputableWeightPolynomial.presentation t) =
      balance (ComputableWeightPolynomial.coefficient t) := by
  rw [root_formula]
  congr 1
  funext w
  exact ComputableWeightPolynomial.presentation_apply t w

/-- A finite symbolic coefficient condition, independent of the residual
flavor matrices. Repeated exterior terms are kept abstract in the proof. -/
def Occurs (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) : Prop :=
  balance (ComputableWeightPolynomial.coefficient (SMComputableCharacter.terms c m delta)) ≠ 0

theorem occurs_iff (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) :
    Occurs c m delta ↔ SMComputableCharacter.multiplicity c m delta ≠ 0 := by
  rw [Occurs,← root_formula]
  rfl

noncomputable section

local instance compactMeasurable : MeasurableSpace SMCombinedCompactAction.Group := borel _
local instance compactBorel : BorelSpace SMCombinedCompactAction.Group := ⟨rfl⟩

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

theorem presents (m : ℕ) (delta : ℤ) : CompactWeylExtraction.Presents
    (SMCombinedCompactContinuity.model flavor p m delta) inclusion.toMonoidHom monomial
    (SMComputableCharacter.polynomial (SMIteratedContent.counts p) m delta) := by
  intro t
  exact (SMComputableCharacter.terms_evaluation flavor p m delta t).symm.trans
    (ComputableWeightPolynomial.presentation_evaluate (fun w => monomial w t)
      (SMComputableCharacter.terms (SMIteratedContent.counts p) m delta)).symm

theorem local_allowed_iff (m : ℕ) (delta : ℤ)
    (input : SMCompactMultiplicity.Input flavor p m delta) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor p m delta)) ↔
      Occurs (SMIteratedContent.counts p) m delta := by
  have ha := SMWeylExtractionInput.local_allowed_iff flavor p m delta
    (SMCombinedCompactContinuity.model flavor p m delta) inclusion.toMonoidHom monomial roots
    (SMCombinedCompactContinuity.coefficientEquiv flavor p m delta)
    (SMCombinedCompactContinuity.continuous_model flavor p m delta) input
    (SMComputableCharacter.polynomial (SMIteratedContent.counts p) m delta)
    (presents flavor p m delta)
  have hn := SMWeylExtractionInput.multiplicity_nonnegative flavor p m delta
    (SMCombinedCompactContinuity.model flavor p m delta) inclusion.toMonoidHom monomial roots
    (SMCombinedCompactContinuity.coefficientEquiv flavor p m delta)
    (SMCombinedCompactContinuity.continuous_model flavor p m delta) input
    (SMComputableCharacter.polynomial (SMIteratedContent.counts p) m delta)
    (presents flavor p m delta)
  have hz : (0 < CompactWeylExtraction.constantTerm roots
      (SMComputableCharacter.polynomial (SMIteratedContent.counts p) m delta)) ↔
      (CompactWeylExtraction.constantTerm roots
        (SMComputableCharacter.polynomial (SMIteratedContent.counts p) m delta)) ≠ 0 := by omega
  exact ha.trans (hz.trans (Iff.of_eq (congrArg (fun z : ℤ => z ≠ 0)
    (terms_balance (SMComputableCharacter.terms (SMIteratedContent.counts p) m delta)))))

/-- This discharges the remaining color/hypercharge Hom of the canonical
joint multiplicity for the actual coefficient target. -/
theorem joint_allowed_iff (m : Fin (SMContentWeakBound.bound p+1)) (delta : ℤ)
    (input : SMCompactMultiplicity.Input flavor p m.val delta) :
    SelectionCriteria.Allowed (IntertwiningMap
      (SMJointSpinContent.jointMultiplicity flavor p m.val 0 0) (SMJointCoefficient.line delta)) ↔
      Occurs (SMIteratedContent.counts p) m.val delta :=
  (SMJointCoefficient.local_allowed_iff flavor p m delta).symm.trans
    (local_allowed_iff flavor p m.val delta input)

/-- Eliminates the existential opaque block-equivalence test from the
previous finite-constituent consumer, collectively over its complete blocks. -/
theorem matches_iff (m : ℕ) (delta : ℤ)
    (input : SMCompactMultiplicity.Input flavor p m delta) :
    (∃ i, SMFiniteConstituentSupport.Matches flavor p m delta i) ↔
      Occurs (SMIteratedContent.counts p) m delta :=
  (SMFiniteConstituentSupport.local_allowed_iff flavor p m delta).symm.trans
    (local_allowed_iff flavor p m delta input)

theorem kernel_allowed_iff (m : ℕ) (delta : ℤ)
    (input : SMCompactMultiplicity.Input flavor p m delta) :
    SelectionCriteria.Allowed (SMFullLocalKernel.Kernel flavor p m delta) ↔
      Occurs (SMIteratedContent.counts p) m delta :=
  (SelectionCriteria.allowed_equiv (SMFullLocalKernel.coefficientEquiv flavor p m delta)).symm.trans
    (local_allowed_iff flavor p m delta input)

variable {k : ℕ} [NeZero k] (q l : ZMod k)

theorem ql_test_iff (m : ℕ) (delta : ℤ)
    (input : SMQLCompactMultiplicity.Input q l p m delta) :
    SelectionCriteria.Allowed (QLFiniteSupport.Test q l p m delta) ↔
      QLFiniteSupport.charge q l p = 0 ∧ Occurs (SMIteratedContent.counts p) m delta :=
  (QLFiniteSupport.test_allowed_iff q l p m delta).trans
    (and_congr Iff.rfl (local_allowed_iff (QLFiniteSupport.flavor q l) p m delta input))

theorem original_ql_iff (h d : ℕ)
    (input : ∀ m : Fin (SMContentWeakBound.bound p+1),
      SMQLCompactMultiplicity.Input q l p m.val ((h : ℤ)-d)) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
      QLFiniteSupport.charge q l p = 0 ∧
        ∃ m : Fin (SMContentWeakBound.bound p+1), BoundedHiggsSupport.Admissible h d m.val ∧
          Occurs (SMIteratedContent.counts p) m.val ((h : ℤ)-d) :=
  (QLFiniteSupport.original_allowed_iff q l p h d).trans
    (and_congr Iff.rfl (exists_congr (fun m => and_congr Iff.rfl
      (local_allowed_iff (QLFiniteSupport.flavor q l) p m.val _ (input m)))))

theorem original_ql_forbidden (h d : ℕ)
    (input : ∀ m : Fin (SMContentWeakBound.bound p+1),
      SMQLCompactMultiplicity.Input q l p m.val ((h : ℤ)-d)) :
    SelectionCriteria.Forbidden (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
      ¬ (QLFiniteSupport.charge q l p = 0 ∧
        ∃ m : Fin (SMContentWeakBound.bound p+1), BoundedHiggsSupport.Admissible h d m.val ∧
          Occurs (SMIteratedContent.counts p) m.val ((h : ℤ)-d)) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,original_ql_iff p q l h d input]

end
end Physics.SMJointAlgebraicSupport
