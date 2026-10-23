import Physics.StandardModel.Operators.Support.Lepton.SMLeptonCoreBranching
import Physics.StandardModel.Operators.Support.Joint.SMSignedHiggsSupport

/-! Maximal spin-zero weak components at every fitting even L/dual-L
degree, including complementary occupations. These local constituents
are not by themselves asserted admissible in an isolated Higgs operator. -/
namespace Physics.SMLeptonMaximalLocal
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

@[reducible] local instance (a b : ℕ) : AddCommGroup (SU2PairExterior.PairCarrier a b) := inferInstance

def weakEquiv (m : ℕ) : Representation.Equiv
    ((SU2PairExterior.pair m 0).comp SMLeptonCoreBranching.projection)
    (SMGenerationCauchy.weak.symmetricPower m) where
  toLinearEquiv := (SU2PairExterior.rightZero m).toLinearEquiv
  isIntertwining' g := (SU2PairExterior.rightZero m).isIntertwining' (SMLeptonCoreBranching.projection g)

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

theorem positive (n : ℕ) (hn : n≤12) (he : n%2=0) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (SMLowerGenerationSupport.pattern 3 n)
        (min n (12-n)) (n : ℤ))) := by
  let p := SMLowerGenerationSupport.pattern 3 n
  let m := min n (12-n)
  let source := (SMCombinedCompactAction.source flavor p).comp SMGenerationCauchy.inclusion
  have hb : SU2PairGenerationBounds.Bounds n m 0 := by
    unfold SU2PairGenerationBounds.Bounds
    dsimp [m]
    omega
  have hh := (SMLeptonCoreBranching.source_target_iff flavor n m 0).mpr hb
  have hh' : SelectionCriteria.Allowed (IntertwiningMap source (SMGenerationCauchy.weak.symmetricPower m)) :=
    (SelectionCriteria.allowed_equiv (InvariantTensorCurry.postcompose source _ (weakEquiv m))).mp hh
  have hd : SelectionCriteria.Allowed (IntertwiningMap source (SMGenerationCauchy.weak.symmetricPower m).dual) :=
    (SelectionCriteria.allowed_equiv (InvariantTensorCurry.postcompose source _
      (SMGenerationCoefficients.weakDuality m))).mp hh'
  have hc := (SelectionCriteria.allowed_equiv (InvariantTensorCurry.equiv source
    (SMGenerationCauchy.weak.symmetricPower m))).mpr hd
  have hr := (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (SMGenerationCoefficients.actionEquiv flavor p m (n : ℤ)))).mp hc
  have hcharge : SMContentWeakBound.hypercharge p+3*(n : ℤ)=0 := by
    rw [SMLowerGenerationSupport.lepton_charge]
    ring
  have hf := SMCombinedChargeSupport.allowed flavor p m (n : ℤ) hcharge hr
  exact (SelectionCriteria.allowed_equiv
    ((SMCombinedCompactAction.coefficientEquiv flavor p m (n : ℤ)).trans
      (SMMixedCompactCoefficients.localEquiv flavor p m (n : ℤ)).symm)).mp hf

theorem negative (n : ℕ) (hn : n≤12) (he : n%2=0) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (SMLowerGenerationSupport.pattern 8 n)
        (min n (12-n)) (-(n : ℤ)))) := by
  exact (SelectionCriteria.allowed_equiv (SMSignedHiggsSupport.coefficientEquiv flavor 3 n
    (min n (12-n)) (n : ℤ))).mp (positive flavor n hn he)

end
end Physics.SMLeptonMaximalLocal
