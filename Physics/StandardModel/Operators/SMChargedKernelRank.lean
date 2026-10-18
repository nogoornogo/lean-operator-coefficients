import Physics.StandardModel.Operators.SMFullLocalKernel

/-! Exact full column rank for hypercharge-incompatible actual local matrices. -/
namespace GUT.SMChargedKernelRank
set_option autoImplicit false
noncomputable section
open Math Representation SMIntegralLocalWeights
variable {H : Type*} [_root_.Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (m : ℕ) (delta : ℤ)

theorem local_charge
    (h : SelectionCriteria.Allowed
      (InvariantCoefficientTransport.Invariants (action flavor p m delta))) :
    SMContentWeakBound.hypercharge p + 3*delta = 0 :=
  InvariantTensorCharge.charge_zero (source flavor p) (boson (H := H) m delta)
    hyper (SMContentWeakBound.hypercharge p) (3*delta)
    (SMContentWeakBound.source_hypercharge flavor p)
    (SMFiniteHiggsSupport.constituent_hypercharge m delta) h

theorem full_rank (h : SMContentWeakBound.hypercharge p + 3*delta ≠ 0) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) =
      Fintype.card (Fin (Module.finrank ℂ (SMFullLocalKernel.Carrier flavor p m))) := by
  have hn : ¬ SelectionCriteria.Allowed
      (InvariantCoefficientTransport.Invariants (action flavor p m delta)) :=
    fun ha => h (local_charge flavor p m delta ha)
  have hlo := not_lt.mp (fun hr => hn
    ((SMFullLocalKernel.allowed_iff_rank_lt flavor p m delta).mpr hr))
  have hhi := LinearMap.finrank_range_le (SMFullLocalKernel.constraints flavor p m delta)
  have hd : Module.finrank ℂ
      (Fin (Module.finrank ℂ (SMFullLocalKernel.Carrier flavor p m)) → ℂ) =
      Fintype.card (Fin (Module.finrank ℂ (SMFullLocalKernel.Carrier flavor p m))) := by
    simp
  exact le_antisymm (hhi.trans_eq hd) hlo

theorem dimension_zero_above_cutoff (hn : 180 < n) :
    Module.finrank ℂ (SMFullLocalKernel.Carrier flavor p m) = 0 := by
  let : Subsingleton (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) :=
    ⟨fun x y => Subtype.ext ((ThreeGenerationFermionBound.exterior_zero n hn x.val).trans
      (ThreeGenerationFermionBound.exterior_zero n hn y.val).symm)⟩
  apply Module.finrank_zero_of_subsingleton

/-- Above the actual fermion cutoff the matrix has zero columns and rank zero. -/
theorem rank_zero_above_cutoff (hn : 180 < n) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) = 0 := by
  have hd := dimension_zero_above_cutoff flavor p m hn
  have he := LinearMap.finrank_range_le (SMFullLocalKernel.constraints flavor p m delta)
  have hb : Module.finrank ℂ
      (Fin (Module.finrank ℂ (SMFullLocalKernel.Carrier flavor p m)) → ℂ) =
      Module.finrank ℂ (SMFullLocalKernel.Carrier flavor p m) := by simp
  exact Nat.eq_zero_of_le_zero (he.trans_eq (hb.trans hd))

end
end GUT.SMChargedKernelRank
