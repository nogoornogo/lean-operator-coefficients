import Physics.StandardModel.Operators.DipoleSMCoefficient
import Math.LinearAlgebra.StatisticalCompleteness

open Math

/-! The prescribed ordered dipole channels have no repeated-field exchange
generators. They are the empty-generator specialization, not an exterior sector.
Finite dimension remains confined to the existing electron-dual/Hom adapter. -/
namespace GUT.DipolePermutationCompleteness
set_option autoImplicit false
noncomputable section
open Representation
variable {H A B : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [FiniteDimensional ℂ B]
  (a : Representation ℂ H A) (b : Representation ℂ H B)

def equiv : (DipoleSMCoefficient.SectorB a b × DipoleSMCoefficient.SectorW a b) ≃ₗ[ℂ]
    (IntertwiningMap a b × IntertwiningMap a b) :=
  StatisticalCompleteness.noExchanges (DipoleSMCoefficient.equiv a b)

theorem equiv_agrees : equiv a b = DipoleSMCoefficient.equiv a b :=
  StatisticalCompleteness.noExchanges_agrees _

theorem inverse_agrees : (equiv a b).symm = (DipoleSMCoefficient.equiv a b).symm := by
  rw [equiv_agrees]

end
end GUT.DipolePermutationCompleteness
