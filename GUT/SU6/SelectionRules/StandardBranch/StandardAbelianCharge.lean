import Physics.StandardModel.Spectrum.ChargeResolved
import GUT.SU6.Characters.AmbientCharacterBridge
import GUT.SU6.SelectionRules.StandardBranch.StandardBranchProtonObstruction
import GUT.SU6.Branching.StandardSU5Orbit

open Math

/-!
# SU(6) source adapters for charge-resolved standard-branch characters

The rank-four normalization and coefficient algebra are re-exported from
GUT.SU5.Branching.ChargeResolved, independently of this ambient source.
-/

open scoped BigOperators

namespace GUT
namespace StandardAbelianCharge

open StandardSU5Orbit

noncomputable section

/-!
## The ambient `SU(6)` source bridge
-/

/-- Extend an `S_5` permutation by fixing the sixth coordinate. -/
def liftPerm (sigma : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 6) :=
  sigma.viaFintypeEmbedding Fin.castSuccEmb

@[simp]
theorem liftPerm_apply_castSucc
    (sigma : Equiv.Perm (Fin 5)) (i : Fin 5) :
    liftPerm sigma i.castSucc = (sigma i).castSucc := by
  change
    sigma.viaFintypeEmbedding Fin.castSuccEmb (Fin.castSuccEmb i) =
      Fin.castSuccEmb (sigma i)
  exact Equiv.Perm.viaFintypeEmbedding_apply_image sigma Fin.castSuccEmb i

@[simp]
theorem liftPerm_apply_last (sigma : Equiv.Perm (Fin 5)) :
    liftPerm sigma (Fin.last 5) = Fin.last 5 := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  simp

@[simp]
theorem liftPerm_symm (sigma : Equiv.Perm (Fin 5)) :
    (liftPerm sigma).symm = liftPerm sigma.symm := by
  rfl

theorem ambient_permuteExponent_liftPerm
    (sigma : Equiv.Perm (Fin 5)) (e : RawWeight) :
    AmbientWeightLattice.permuteExponent (liftPerm sigma) e =
      StandardSU5Orbit.permuteWeight sigma e := by
  funext i
  rw [AmbientWeightLattice.permuteExponent,
    StandardSU5Orbit.permuteWeight, liftPerm_symm,
    liftPerm_apply_castSucc, liftPerm_apply_last,
    AmbientWeightLattice.rawCoord_castSucc,
    AmbientWeightLattice.rawCoord_last, sub_zero]

theorem standardWeylInvariant_of_ambient
    (p : AmbientWeightLattice.Character)
    (hp : AmbientWeightLattice.IsWeylInvariant p) :
    StandardSU5Orbit.WeylInvariant p := by
  intro sigma
  have h := hp (liftPerm sigma)
  unfold AmbientWeightLattice.permuteCharacter at h
  unfold StandardSU5Orbit.permute
  rw [show AmbientWeightLattice.permuteExponent (liftPerm sigma) =
      StandardSU5Orbit.permuteWeight sigma by
    funext e
    exact ambient_permuteExponent_liftPerm sigma e] at h
  exact h

theorem actualModel_chargeProfiles_equal
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    {rho : Representation ℂ ActualRestriction.SU6 V}
    (M : AmbientCharacterBridge.ActualAmbientLaurentModel rho)
    {A : Type*} [AddCommGroup A] (charge : ℤ →+ A) :
    let p := chargeResolved charge M.poly
    quarkProfile p = upProfile p ∧
      quarkProfile p = electronProfile p ∧
      downProfile p = leptonProfile p := by
  dsimp
  apply sm_charge_profiles_equal
  apply chargeResolved_isWeylInvariant
  exact standardWeylInvariant_of_ambient M.poly M.isWeylInvariant

theorem virtualModel_chargeProfiles_equal
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    {A : Type*} [AddCommGroup A] (charge : ℤ →+ A) :
    let p := chargeResolved charge M.poly
    quarkProfile p = upProfile p ∧
      quarkProfile p = electronProfile p ∧
      downProfile p = leptonProfile p := by
  dsimp
  apply sm_charge_profiles_equal
  apply chargeResolved_isWeylInvariant
  exact standardWeylInvariant_of_ambient M.poly M.isWeylInvariant

theorem virtualModel_exists_supported_neutral_proton_sectors
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    {A : Type*} [AddCommGroup A] (charge : ℤ →+ A)
    (hTen : quarkProfile (chargeResolved charge M.poly) ≠ 0)
    (hBarFive : downProfile (chargeResolved charge M.poly) ≠ 0) :
    ∃ k : StandardBranchProtonObstruction.Charges A,
      ChargesSupported (chargeResolved charge M.poly) k ∧
        StandardBranchProtonObstruction.protonFirst k = 0 ∧
        StandardBranchProtonObstruction.protonSecond k = 0 := by
  apply exists_supported_neutral_proton_sectors
  · apply chargeResolved_isWeylInvariant
    exact standardWeylInvariant_of_ambient M.poly M.isWeylInvariant
  · exact hTen
  · exact hBarFive

theorem finiteAbelian_virtualModel_exists_supported_neutral_proton_sectors
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    {A : Type*} [AddCommGroup A] [Finite A] (charge : ℤ →+ A)
    (hTen : quarkProfile (chargeResolved charge M.poly) ≠ 0)
    (hBarFive : downProfile (chargeResolved charge M.poly) ≠ 0) :
    ∃ k : StandardBranchProtonObstruction.Charges A,
      ChargesSupported (chargeResolved charge M.poly) k ∧
        StandardBranchProtonObstruction.protonFirst k = 0 ∧
        StandardBranchProtonObstruction.protonSecond k = 0 :=
  virtualModel_exists_supported_neutral_proton_sectors M charge hTen hBarFive

/-- Concrete finite cyclic specialization of the family-dependent standard charge-orbit bridge to Abelian proton-operator neutrality
conclusion.  Integer lifts that agree modulo `N` have already been summed by
`chargeResolved`. -/
theorem cyclicResidual_virtualModel_exists_supported_neutral_proton_sectors
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    (N : ℕ) [NeZero N]
    (hTen : quarkProfile
      (chargeResolved (cyclicCharge N) M.poly) ≠ 0)
    (hBarFive : downProfile
      (chargeResolved (cyclicCharge N) M.poly) ≠ 0) :
    ∃ k : StandardBranchProtonObstruction.Charges (ZMod N),
      ChargesSupported (chargeResolved (cyclicCharge N) M.poly) k ∧
        StandardBranchProtonObstruction.protonFirst k = 0 ∧
        StandardBranchProtonObstruction.protonSecond k = 0 :=
  finiteAbelian_virtualModel_exists_supported_neutral_proton_sectors
    M (cyclicCharge N) hTen hBarFive


open StandardBranchProtonObstruction

theorem proton_functionals_eq_zero_of_virtualModel_pureSM
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    {A : Type*} [AddCommGroup A] (charge : ℤ →+ A)
    (generations : ℤ) (hgenerations : generations ≠ 0)
    (k : Charges A)
    (hSM : IsPureSMChargeSpectrum
      (chargeResolved charge M.poly) generations k) :
    protonFirst k = 0 ∧ protonSecond k = 0 := by
  apply proton_functionals_eq_zero_of_pureSM
    (chargeResolved charge M.poly)
  · apply chargeResolved_isWeylInvariant
    exact standardWeylInvariant_of_ambient M.poly M.isWeylInvariant
  · exact hgenerations
  · exact hSM

/-- Explicit finite-Abelian specialization. -/
theorem finiteAbelian_proton_functionals_eq_zero_of_virtualModel_pureSM
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    {A : Type*} [AddCommGroup A] [Finite A] (charge : ℤ →+ A)
    (generations : ℤ) (hgenerations : generations ≠ 0)
    (k : Charges A)
    (hSM : IsPureSMChargeSpectrum
      (chargeResolved charge M.poly) generations k) :
    protonFirst k = 0 ∧ protonSecond k = 0 :=
  proton_functionals_eq_zero_of_virtualModel_pureSM M charge
    generations hgenerations k hSM

/-- Concrete finite cyclic residual-symmetry specialization. -/
theorem cyclicResidual_proton_functionals_eq_zero_of_virtualModel_pureSM
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    (N : ℕ) [NeZero N]
    (generations : ℤ) (hgenerations : generations ≠ 0)
    (k : Charges (ZMod N))
    (hSM : IsPureSMChargeSpectrum
      (chargeResolved (cyclicCharge N) M.poly) generations k) :
    protonFirst k = 0 ∧ protonSecond k = 0 :=
  proton_functionals_eq_zero_of_virtualModel_pureSM M (cyclicCharge N)
    generations hgenerations k hSM

end
end StandardAbelianCharge
end GUT
