import Physics.StandardModel.Operators.Support.Decomposition.SMFiniteConstituentSupport
import Physics.StandardModel.Operators.Support.Coordinates.SMConstantWeakCapacity
import Math.RepresentationTheory.SU2.SU2FiniteBranching

/-! Complete bounded weak-SU2 branching of actual statistical sources.
These are restrictions to weak SU2: the equivalence does not assert that the
chosen copies separately preserve the commuting color, spin or residual action. -/
namespace Physics.SMFiniteWeakBranching
set_option autoImplicit false
noncomputable section
open Math Representation BoundedTorusWeights ContinuousRepresentationScope

abbrev inclusion := SMFiniteConstituentSupport.weakInclusion

theorem inclusion_continuous : Continuous inclusion :=
  (continuous_const.prodMk (continuous_id.prodMk continuous_const)).prodMk continuous_const

def continuousInclusion : TauCeti.SU2 →ₜ* SMCombinedCompactAction.Group :=
  ⟨inclusion, inclusion_continuous⟩

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

abbrev source := (SMCombinedCompactContinuity.sourceModel flavor p).comp inclusion

theorem source_continuous : IsJointlyContinuous (source flavor p) :=
  (SMCombinedCompactContinuity.source_continuous flavor p).comp continuousInclusion

theorem source_restrict : (SMCombinedCompactAction.source flavor p).comp inclusion =
    (SMContentWeakBound.source flavor p).comp WeakSingletHiggsSupport.weakInclusion := by
  have h := SMCombinedCompactAction.source_gauge flavor p
  let j : TauCeti.SU2 →* StandardSMGaugeTensor.GaugeGroup :=
    (MonoidHom.inr _ _).comp (MonoidHom.inl _ _)
  exact congrArg (fun r => r.comp j) h

def modelEquiv : Representation.Equiv
    ((SMContentWeakBound.source flavor p).comp WeakSingletHiggsSupport.weakInclusion)
    (source flavor p) := by
  rw [← source_restrict flavor p]
  exact SplitRepresentationProjection.restrictEquiv
    (ContinuousUnitaryConstructions.basisCopyRepresentationEquiv
      (SMCombinedCompactContinuity.sourceBasis flavor p)
      (SMCombinedCompactAction.source flavor p)) inclusion

theorem source_bounded : Bounded (source flavor p) TauCeti.SU2.torusHom
    (SMContentWeakBound.bound p) := by
  have hb := bounded_comp (SMContentWeakBound.source flavor p)
    WeakSingletHiggsSupport.weakInclusion TauCeti.SU2.torusHom
    (SMContentWeakBound.bound p) (SMContentWeakBound.source_bounded flavor p)
  exact SU2FiniteBranching.transport_bound (SMContentWeakBound.bound p) (modelEquiv flavor p) hb

/-- All weak nonsinglets occur among these bounded, actual irreducible copies. -/
def certificate : SU2FiniteBranching.Certificate (source flavor p) (SMContentWeakBound.bound p) :=
  (SU2FiniteBranching.exists_certificate _ _ (source_continuous flavor p)
    (source_bounded flavor p)).some

theorem constant_bounded (s : DeltaLOneSignedInput.Species) (r : ℕ) :
    Bounded (source flavor (SMConstantWeakCapacity.pattern s r)) TauCeti.SU2.torusHom
      (SMConstantWeakCapacity.bound s r) := by
  have hb := bounded_comp (SMContentWeakBound.source flavor (SMConstantWeakCapacity.pattern s r))
    WeakSingletHiggsSupport.weakInclusion TauCeti.SU2.torusHom
    (SMConstantWeakCapacity.bound s r) (SMConstantWeakCapacity.source_bounded flavor s r)
  exact SU2FiniteBranching.transport_bound (SMConstantWeakCapacity.bound s r)
    (modelEquiv flavor (SMConstantWeakCapacity.pattern s r)) hb

/-- The complementary-exterior cutoff bounds the labels of a complete sum,
not just a selected weak-singlet coefficient sector. -/
def constantCertificate (s : DeltaLOneSignedInput.Species) (r : ℕ) :
    SU2FiniteBranching.Certificate (source flavor (SMConstantWeakCapacity.pattern s r))
      (SMConstantWeakCapacity.bound s r) :=
  (SU2FiniteBranching.exists_certificate _ _
    (source_continuous flavor (SMConstantWeakCapacity.pattern s r))
    (constant_bounded flavor s r)).some

end
end Physics.SMFiniteWeakBranching
