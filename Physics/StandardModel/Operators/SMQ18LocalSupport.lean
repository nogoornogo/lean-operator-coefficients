import Physics.StandardModel.Operators.SMQ18Support
import Physics.StandardModel.Operators.SMCombinedChargeSupport

/-! Restore hypercharge and transport structural Q18 witnesses to actual kernels. -/
namespace GUT.SMQ18LocalSupport
set_option autoImplicit false
noncomputable section
open Math Representation SMGenerationCauchy
open scoped TensorProduct

def flavor (s : DeltaLOneSignedInput.Species) :
    Representation ℂ Unit (ThreeGenerationFermionBound.Flavor s) := trivial ℂ Unit _
def pattern (_ : Fin 18) : DeltaLOneSignedInput.Species := 0

@[reducible] local instance : AddCommGroup
    (SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ]
      WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup SMQ18Support.Field := inferInstance

def sourceEquiv (n : ℕ) : Representation.Equiv (SMQ18Support.rho.exteriorPower n)
    ((SMCombinedCompactAction.source flavor (fun _ : Fin n => 0)).comp inclusion) where
  toLinearEquiv := ConstantPatternExterior.linearEquiv SMCombinedCompactAction.field 0 n
  isIntertwining' g := by
    have hr := congrArg (fun r : Representation ℂ Group SMQ18Support.Field => r g) actual_quark
    have he : SMQ18Support.rho.exteriorPower n g =
        (SMCombinedCompactAction.field 0).exteriorPower n (inclusion g) := by
      change exteriorPower.map n (SMQ18Support.rho g) =
        exteriorPower.map n (SMCombinedCompactAction.field 0 (inclusion g))
      exact congrArg (exteriorPower.map n) hr.symm
    rw [he]
    exact (ConstantPatternExterior.equiv SMCombinedCompactAction.field 0 n).isIntertwining'
      (inclusion g)

theorem boson_restrict (m : ℕ) (delta : ℤ) :
    (SMCombinedCompactAction.boson (H := Unit) m delta).comp inclusion = weak.symmetricPower m := by
  ext g : 1
  apply LinearMap.ext
  intro x
  have hc : SMHiggsConstituents.character (H := Unit)
      (SMCombinedCompactAction.gaugeEmbedding (inclusion g)) = 1 := by
    apply Units.ext
    simp [SMHiggsConstituents.character_apply, SMCombinedCompactAction.gaugeEmbedding,
      SMMixedCompactCoefficients.retained, inclusion, StandardSMGaugeTensor.phase]
  change (((SMHiggsConstituents.character ^ delta)
    (SMCombinedCompactAction.gaugeEmbedding (inclusion g)) : ℂˣ) •
      (WeakDoubletScalars.doublet.symmetricPower m) g.2.1 x) = _
  simp only [MonoidHom.zpow_apply, hc, one_zpow, one_smul]
  rfl

def bosonEquiv (m : ℕ) (delta : ℤ) : Representation.Equiv (weak.symmetricPower m)
    ((SMCombinedCompactAction.boson (H := Unit) m delta).comp inclusion) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by rw [boson_restrict]; rfl

def actionEquiv (n m : ℕ) (delta : ℤ) : Representation.Equiv
    ((SMQ18Support.rho.exteriorPower n).tprod (weak.symmetricPower m))
    ((SMCombinedCompactAction.action flavor (fun _ : Fin n => 0) m delta).comp inclusion) where
  toLinearEquiv := TensorProduct.congr (sourceEquiv n).toLinearEquiv
    (bosonEquiv m delta).toLinearEquiv
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    change sourceEquiv n (SMQ18Support.rho.exteriorPower n g x) ⊗ₜ[ℂ]
      bosonEquiv m delta (weak.symmetricPower m g y) = _
    exact congrArg₂ (fun a b => a ⊗ₜ[ℂ] b)
      ((sourceEquiv n).toIntertwiningMap.isIntertwining _ _ g x)
      ((bosonEquiv m delta).toIntertwiningMap.isIntertwining _ _ g y)

theorem restricted_allowed (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 18) (delta : ℤ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((SMCombinedCompactAction.action flavor pattern m delta).comp inclusion)) :=
  (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (actionEquiv 18 m delta))).mp (SMQ18Support.semisimple_allowed m hm hmax)

theorem charge : SMContentWeakBound.hypercharge pattern = 18 := by
  simp [SMContentWeakBound.hypercharge, pattern, DeltaLOneSignedInput.hypercharge]

theorem compact_allowed (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 18) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMCombinedCompactAction.action flavor pattern m (-6))) :=
  SMCombinedChargeSupport.allowed flavor pattern m (-6) (by rw [charge]; norm_num)
    (restricted_allowed m hm hmax (-6))

theorem kernel_allowed (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 18) :
    SelectionCriteria.Allowed (SMFullLocalKernel.Kernel flavor pattern m (-6)) :=
  (SelectionCriteria.allowed_equiv
    ((SMCombinedCompactAction.coefficientEquiv flavor pattern m (-6)).trans
      (SMMixedCompactCoefficients.kernelEquiv flavor pattern m (-6)))).mp
    (compact_allowed m hm hmax)

theorem q18 : SelectionCriteria.Allowed (SMFullLocalKernel.Kernel flavor pattern 6 (-6)) :=
  kernel_allowed 6 (by omega) (by omega)

theorem local_allowed (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 18) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor pattern m (-6))) :=
  (SelectionCriteria.allowed_equiv (SMFullLocalKernel.coefficientEquiv
    flavor pattern m (-6))).mpr (kernel_allowed m hm hmax)

theorem kernel_positive (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 18) :
    0 < Module.finrank ℂ (SMFullLocalKernel.Kernel flavor pattern m (-6)) :=
  (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)).mpr (kernel_allowed m hm hmax)

theorem rank_deficient (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 18) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor pattern m (-6))) <
      Module.finrank ℂ (SMFullLocalKernel.Carrier flavor pattern m) := by
  simpa only [Fintype.card_fin] using
    (SMFullLocalKernel.allowed_iff_rank_lt flavor pattern m (-6)).mp
      (local_allowed m hm hmax)

end
end GUT.SMQ18LocalSupport
