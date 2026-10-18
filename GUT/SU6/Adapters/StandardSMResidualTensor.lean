import Physics.StandardModel.Gauge.ResidualGaugeTensor
import GUT.SU6.SelectionRules.StandardBranch.FiniteAbelianChargeSectors

open Math

/-!
# Compatibility entry point for the SU(6) residual tensor source adapter

Import ResidualGaugeTensor instead for the SU(6)-independent tensor API.
This legacy path retains every former declaration, including the UV source
specialization, without adding that specialization to the shared core.
-/

set_option autoImplicit false

namespace GUT.StandardSMResidualTensor

noncomputable section

open StandardSMGaugeTensor FiniteAbelianChargeSectors StandardBranchProtonObstruction

variable {H : Type*} [CommGroup H]

/-- The existing standard charge-orbit bridge -> Abelian proton-operator neutrality source supplies actual nonzero invariant gauge tensors
on the standard field representations, not yet on its own mass radical. -/
theorem source_invariant_tensors
    (S : StandardPhysicalSource.PureSMChargedSource (ChargeLabel H)) :
    qque ≠ 0 ∧ duql ≠ 0 ∧
      (∀ g x, qque (qqueRepresentation S.charges g x) = qque x) ∧
      (∀ g x, duql (duqlRepresentation S.charges g x) = duql x) := by
  obtain ⟨hFirst, hSecond⟩ := residual_protonCharacters_eq_one S
  exact ⟨qque_nonzero, duql_nonzero,
    (qque_invariant_iff _).mpr hFirst, (duql_invariant_iff _).mpr hSecond⟩

end

end GUT.StandardSMResidualTensor
