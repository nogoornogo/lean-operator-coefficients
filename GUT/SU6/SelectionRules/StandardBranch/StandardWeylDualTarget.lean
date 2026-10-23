import Physics.StandardModel.Spectrum.Representations.SMChiralIndex
import GUT.SU6.SelectionRules.Models.StandardPhysicalSpectrumBridge
import Physics.FieldTheory.Mass.Algebra.InvariantWeylMass

open Physics

open Math

/-!
# Charge-resolved dual indices and the standard-branch orbit argument

Dualization reverses both the normalized gauge weight and the residual
charge. The oriented SM weights are disjoint from their negatives, so their
charge profiles survive antisymmetrization even for groups with two-torsion.
This does not reconstruct self-dual sectors or the signed Dirac index.
-/

set_option autoImplicit false

namespace GUT.StandardWeylDualTarget
open Physics.StandardWeylDualTarget

noncomputable section

open StandardAbelianCharge StandardSMCharacterTarget
open StandardPhysicalSpectrumBridge StandardBranchProtonObstruction

variable {A : Type*} [AddCommGroup A]


omit [AddCommGroup A] in
theorem exactSMWithSinglets_apply_neg_smWeight
    (n : ℤ) (k : Charges A) (s : A →₀ ℤ) (i : Fin 15) (q : A) :
    exactSMWithSingletsResolvedCharacter n k s (-smReducedWeight i, q) = 0 := by
  have hkey : (-smReducedWeight i, q) ∉ Set.range (smResolvedKey k) := by
    rintro ⟨j, hj⟩
    exact smReducedWeight_ne_neg j i (congrArg Prod.fst hj)
  have hw : -smReducedWeight i ≠ 0 := neg_ne_zero.mpr (smReducedWeight_ne_zero i)
  simp only [exactSMWithSingletsResolvedCharacter, Finsupp.add_apply]
  rw [exactSMResolvedCharacter_apply_of_notMem_range n k _ hkey,
    singletResolvedCharacter_apply_of_weight_ne_zero s hw, add_zero]

/-- Every oriented SM weight retains its entire charge profile. -/
theorem chiralDifference_target_chargeProfile
    (n : ℤ) (k : Charges A) (s : A →₀ ℤ) (i : Fin 15) :
    chargeProfile (chiralDifference (exactSMWithSingletsResolvedCharacter n k s))
        (smReducedWeight i) =
      chargeProfile (exactSMWithSingletsResolvedCharacter n k s) (smReducedWeight i) := by
  ext q
  simp only [chargeProfile_apply, chiralDifference, Finsupp.sub_apply, dualCharacter_apply]
  change _ - exactSMWithSingletsResolvedCharacter n k s (-smReducedWeight i, -q) = _
  rw [exactSMWithSinglets_apply_neg_smWeight, sub_zero]

/-- Only the five probe profiles required by standard charge-orbit bridge are recovered. No equality
of full spectra, or recovery of gauge singlets, is asserted. -/
theorem chiralDifference_target_isPureSMChargeSpectrum
    (n : ℤ) (k : Charges A) (s : A →₀ ℤ) :
    IsPureSMChargeSpectrum
      (chiralDifference (exactSMWithSingletsResolvedCharacter n k s)) n k := by
  have h := exactSMWithSingletsResolvedCharacter_isPureSMChargeSpectrum n k s
  have hQ := chiralDifference_target_chargeProfile n k s 0
  have hU := chiralDifference_target_chargeProfile n k s 8
  have hD := chiralDifference_target_chargeProfile n k s 9
  have hL := chiralDifference_target_chargeProfile n k s 13
  have hE := chiralDifference_target_chargeProfile n k s 14
  rw [(smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl] at hQ
  rw [(smReducedWeight_eq_reducedTenUp_iff 8).mpr rfl] at hU
  rw [(smReducedWeight_eq_reducedBarFiveDown_iff 9).mpr rfl] at hD
  rw [(smReducedWeight_eq_reducedBarFiveLepton_iff 13).mpr rfl] at hL
  rw [(smReducedWeight_eq_reducedTenElectron_iff 14).mpr rfl] at hE
  exact ⟨hQ.trans h.quark, hU.trans h.up, hD.trans h.down,
    hL.trans h.lepton, hE.trans h.electron⟩

/-- Singlet data are antisymmetrized, not recovered. In particular a
self-dual order-two charge contributes zero to this dual index. -/
theorem chiralDifference_target_zeroWeight
    (n : ℤ) (k : Charges A) (s : A →₀ ℤ) (q : A) :
    chiralDifference (exactSMWithSingletsResolvedCharacter n k s) (0, q) =
      s q - s (-q) := by
  have h := IsExactSMOnlyCoefficientSpectrum.of_resolvedCharacter_eq
    (rfl : exactSMWithSingletsResolvedCharacter n k s = _)
  simp only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply,
    Prod.neg_mk, neg_zero, h.singletMultiplicity]

/-- The standard-branch standard charge-orbit bridge orbit equalities follow from an equality of dual
indices, without incorrectly recovering the signed Dirac index. -/
theorem su5OrbitCompatible_of_chiralDifference_target
    (p : ResolvedCharacter A) (hp : ResolvedWeylInvariant p)
    (n : ℤ) (hn : n ≠ 0) (k : Charges A) (s : A →₀ ℤ)
    (htarget : chiralDifference p =
      chiralDifference (exactSMWithSingletsResolvedCharacter n k s)) :
    SU5OrbitCompatible k := by
  apply su5OrbitCompatible_of_pureSM (chiralDifference p)
    (chiralDifference_isWeylInvariant p hp) n hn k
  rw [htarget]
  exact chiralDifference_target_isPureSMChargeSpectrum n k s

/-- standard charge-orbit bridge -> Abelian proton-operator neutrality for the dual target, valid for every additive Abelian charge
group and independent of the continuous-U(1) anomaly argument. -/
theorem proton_functionals_eq_zero_of_chiralDifference_target
    (p : ResolvedCharacter A) (hp : ResolvedWeylInvariant p)
    (n : ℤ) (hn : n ≠ 0) (k : Charges A) (s : A →₀ ℤ)
    (htarget : chiralDifference p =
      chiralDifference (exactSMWithSingletsResolvedCharacter n k s)) :
    protonFirst k = 0 ∧ protonSecond k = 0 :=
  proton_functionals_eq_zero_of_su5OrbitCompatible k
    (su5OrbitCompatible_of_chiralDifference_target p hp n hn k s htarget)

section Evaluation

variable {H : Type*} [CommGroup H]

theorem standardExponent_neg (w : ReducedWeight) :
    standardExponent (-w) = -standardExponent w := by
  ext i
  fin_cases i <;> simp [standardExponent] <;> ring

/-- The polynomial involution agrees with contragredient character
evaluation on the actual gauge-times-residual group. -/
theorem keyMonoidHom_neg (key : ResolvedKey (ChargeLabel H)) (g : CombinedGroup H) :
    keyMonoidHom (-key) g = keyMonoidHom key g⁻¹ := by
  rcases g with ⟨x, h⟩
  change UnitAddTorus.mFourier (standardExponent (-key.1)) x.toAdd *
      (((-key.2).toMul h : Circle) : ℂ) =
    UnitAddTorus.mFourier (standardExponent key.1) (-x.toAdd) *
      ((key.2.toMul h⁻¹ : Circle) : ℂ)
  rw [standardExponent_neg]
  congr 1
  · simp [UnitAddTorus.mFourier, neg_smul]
  · rw [map_inv]
    rfl

theorem eval_dualCharacter (p : ResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (dualCharacter p) x h = eval p (-x) h⁻¹ := by
  classical
  unfold eval dualCharacter
  rw [Finsupp.sum_mapDomain_index]
  · apply Finsupp.sum_congr
    intro key _
    rw [keyMonoidHom_neg]
    rfl
  · intro key
    simp
  · intro key a b
    simp [add_mul]

theorem eval_chiralDifference (p : ResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (chiralDifference p) x h = eval p x h - eval p (-x) h⁻¹ := by
  change StandardPhysicalCharacterBridge.resolvedEvalAddHom x h (p - dualCharacter p) = _
  rw [map_sub]
  change eval p x h - eval (dualCharacter p) x h = _
  rw [eval_dualCharacter]

/-- The normalized dual index evaluates to the actual dual trace difference,
not to the original signed character. -/
theorem eval_chiralDifference_eq_character
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (sigma : Representation ℂ (CombinedGroup H) E)
    (p : ResolvedCharacter (ChargeLabel H))
    (hmodel : ∀ x h, sigma.character (Multiplicative.ofAdd x, h) = eval p x h)
    (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (chiralDifference p) x h =
      sigma.character (Multiplicative.ofAdd x, h) -
        sigma.dual.character (Multiplicative.ofAdd x, h) := by
  rw [eval_chiralDifference, Representation.char_dual]
  rw [← hmodel, ← hmodel]
  rfl

end Evaluation

section MassBridge

open InvariantWeylMass PhysicalRestrictionBridge CompactEmbeddingClassification
open StandardPhysicalSource (FiniteChargedContinuousUnitarySource)
open StandardPhysicalCharacterBridge
  (sourceProductRepresentation sourceProductRepresentation_character)
open FiniteAbelianChargeSectors (centralDegreeCharge)

variable {H : Type*} {E : Type} [CommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {sigma : Representation ℂ (CombinedGroup H) E}

/-- Faithfulness converts the actual radical's dual target into an equality
of normalized dual characters, using the proved mass conservation law. -/
theorem chiralDifference_eq_target_of_mass
    (B : SymmetricMass sigma) (hUnitary : IsUnitaryRepresentation sigma)
    (p : ResolvedCharacter (ChargeLabel H))
    (hmodel : ∀ x h, sigma.character (Multiplicative.ofAdd x, h) = eval p x h)
    (n : ℤ) (k : Charges (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
    (hLight : FiniteVirtualGroupRepresentation.CharacterEquivalent (lightDualIndex B)
      (ofCharacter (chiralDifference (exactSMWithSingletsResolvedCharacter n k s)))) :
    chiralDifference p = chiralDifference (exactSMWithSingletsResolvedCharacter n k s) := by
  apply eval_faithful
  intro x h
  rw [eval_chiralDifference_eq_character sigma p hmodel]
  have hUV := ultravioletDualIndex_characterEquivalent_of_lightDualIndex
    B hUnitary _ hLight (Multiplicative.ofAdd x, h)
  simpa only [dualIndex_character, character_ofCharacter] using hUV

/-- The actual light dual target and a Weyl-invariant UV character imply
the standard charge-orbit bridge charge equalities. The light target remains an explicit IR hypothesis. -/
theorem su5OrbitCompatible_of_mass_dual_target
    (B : SymmetricMass sigma) (hUnitary : IsUnitaryRepresentation sigma)
    (p : ResolvedCharacter (ChargeLabel H)) (hp : ResolvedWeylInvariant p)
    (hmodel : ∀ x h, sigma.character (Multiplicative.ofAdd x, h) = eval p x h)
    (n : ℤ) (hn : n ≠ 0) (k : Charges (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
    (hLight : FiniteVirtualGroupRepresentation.CharacterEquivalent (lightDualIndex B)
      (ofCharacter (chiralDifference (exactSMWithSingletsResolvedCharacter n k s)))) :
    SU5OrbitCompatible k :=
  su5OrbitCompatible_of_chiralDifference_target p hp n hn k s
    (chiralDifference_eq_target_of_mass B hUnitary p hmodel n k s hLight)

/-- Specialization to the existing actual SU(6) charged-sector source. The
source's polynomial model and Weyl invariance are derived, not supplied.
Its identification with the full all-left-handed field representation is
still an explicit interface obligation. The central twist is fixed to one. -/
theorem chargedSource_proton_functionals_eq_zero_of_mass_dual_target
    (B : SymmetricMass sigma) (hUnitary : IsUnitaryRepresentation sigma)
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H))
    (hSource : ∀ x h, sigma.character (Multiplicative.ofAdd x, h) =
      FiniteVirtualGroupRepresentation.character (sourceProductRepresentation 1 source)
        (Multiplicative.ofAdd x, h))
    (n : ℤ) (hn : n ≠ 0) (k : Charges (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
    (hLight : FiniteVirtualGroupRepresentation.CharacterEquivalent (lightDualIndex B)
      (ofCharacter (chiralDifference (exactSMWithSingletsResolvedCharacter n k s)))) :
    protonFirst k = 0 ∧ protonSecond k = 0 := by
  apply proton_functionals_eq_zero_of_su5OrbitCompatible k
  exact su5OrbitCompatible_of_mass_dual_target B hUnitary
    (source.resolvedCharacter (centralDegreeCharge 1))
    (source.resolvedCharacter_isWeylInvariant _)
    (fun x h => (hSource x h).trans (sourceProductRepresentation_character 1 source x h))
    n hn k s hLight

end MassBridge

end

end GUT.StandardWeylDualTarget
