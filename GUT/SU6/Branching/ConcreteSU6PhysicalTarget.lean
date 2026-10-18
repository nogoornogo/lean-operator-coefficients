import GUT.SU6.Branching.ConcreteSU6Branching
import GUT.SU6.SelectionRules.StandardBranch.PhysicalChargeResolvedBridge
import GUT.SU6.Branching.PhysicalSMTorusTarget

open Math

/-!
# Physical Standard Model character of the concrete signed source

At the standard cocharacter `(-2,3)`, the actual analytic source
`15 + bar6 - 6` has exactly one Standard Model generation as its signed
character. This is an index statement, not a claim about a mass map or the
complete zero-mode spectrum.
-/

namespace GUT.ConcreteSU6PhysicalTarget

open scoped BigOperators
open ConcreteSU6Representations ConcreteSU6Branching
open PhysicalTorusCharacterBridge

noncomputable section

/-- Integral weights of the defining representation on the physical torus. -/
def fundamentalExponent : Fin 6 → PhysicalExponent :=
  ![![1, 0, 0, -2], ![0, 1, 0, -2], ![-1, -1, 0, -2],
    ![0, 0, 1, 3], ![0, 0, -1, 3], 0]

theorem physicalDiagonalPoint_last (x : UnitAddTorus (Fin 4)) :
    (physicalDiagonalPoint (-2) 3 x).coords 5 = 1 := by
  have hsum :
      (ambientTorusPoint (-2) 3 x) 0 + (ambientTorusPoint (-2) 3 x) 1 +
        (ambientTorusPoint (-2) 3 x) 2 + (ambientTorusPoint (-2) 3 x) 3 +
        (ambientTorusPoint (-2) 3 x) 4 = 0 := by
    simp [ambientTorusPoint]
    module
  change (((AddCircle.toCircle ((ambientTorusPoint (-2) 3 x) 0) *
    AddCircle.toCircle ((ambientTorusPoint (-2) 3 x) 1) *
    AddCircle.toCircle ((ambientTorusPoint (-2) 3 x) 2) *
    AddCircle.toCircle ((ambientTorusPoint (-2) 3 x) 3) *
    AddCircle.toCircle ((ambientTorusPoint (-2) 3 x) 4))⁻¹ : Circle) : ℂ) = 1
  simp only [← AddCircle.toCircle_add, hsum]
  simp

theorem physicalDiagonalPoint_coords (x : UnitAddTorus (Fin 4)) (i : Fin 6) :
    (physicalDiagonalPoint (-2) 3 x).coords i =
      UnitAddTorus.mFourier (fundamentalExponent i) x := by
  fin_cases i
  all_goals first
    | simpa [fundamentalExponent, UnitAddTorus.mFourier_zero] using
        physicalDiagonalPoint_last x
    | rw [mFourier_eq_toCircle_fourierPairing]
      simp [physicalDiagonalPoint, AmbientLaurent.DiagonalPoint.ofUnitAddTorus,
        AmbientLaurent.DiagonalPoint.coordsOfUnitAddTorus,
        AmbientLaurent.DiagonalPoint.unitAddTorusCoord,
        ambientTorusPoint, fundamentalExponent, fourierPairing, Fin.sum_univ_succ,
        sub_eq_add_neg, add_assoc]

/-- The ten pair weights and five inverse weights in the canonical SM order. -/
theorem smExponent_eq : smExponent =
    ![fundamentalExponent 0 + fundamentalExponent 3,
      fundamentalExponent 0 + fundamentalExponent 4,
      fundamentalExponent 1 + fundamentalExponent 3,
      fundamentalExponent 1 + fundamentalExponent 4,
      fundamentalExponent 2 + fundamentalExponent 3,
      fundamentalExponent 2 + fundamentalExponent 4,
      fundamentalExponent 1 + fundamentalExponent 2,
      fundamentalExponent 0 + fundamentalExponent 2,
      fundamentalExponent 0 + fundamentalExponent 1,
      -fundamentalExponent 0, -fundamentalExponent 1, -fundamentalExponent 2,
      -fundamentalExponent 4, -fundamentalExponent 3,
      fundamentalExponent 3 + fundamentalExponent 4] := by
  decide

theorem mFourier_neg_eq_inv (e : PhysicalExponent) (x : UnitAddTorus (Fin 4)) :
    UnitAddTorus.mFourier (-e) x = (UnitAddTorus.mFourier e x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← UnitAddTorus.mFourier_add, neg_add_cancel, UnitAddTorus.mFourier_zero]
  rfl

theorem eval_integralSMCharacter (x : UnitAddTorus (Fin 4)) :
    eval integralSMCharacter x = ∑ i : Fin 15, UnitAddTorus.mFourier (smExponent i) x := by
  classical
  unfold eval integralSMCharacter
  rw [← Finsupp.sum_finsetSum_index]
  · simp
  · intro e
    simp
  · intro e a b
    simp [add_mul]

theorem ten_add_antifive_eq_SM (x : UnitAddTorus (Fin 4)) :
    tenValue (physicalDiagonalPoint (-2) 3 x).coords +
        (∑ i : Fin 5, ((physicalDiagonalPoint (-2) 3 x).coords i.castSucc)⁻¹) =
      eval integralSMCharacter x := by
  rw [eval_integralSMCharacter, smExponent_eq]
  simp only [tenValue, physicalDiagonalPoint_coords]
  simp [Fin.sum_univ_succ, UnitAddTorus.mFourier_add, mFourier_neg_eq_inv]
  ring

/-- Actual trace equality, with no assumed spectrum certificate. -/
theorem signed_character_physical (x : UnitAddTorus (Fin 4)) :
    exteriorTwo.rho.character (physicalDiagonalPoint (-2) 3 x).toSU6 +
        antifundamental.rho.character (physicalDiagonalPoint (-2) 3 x).toSU6 -
        fundamental.rho.character (physicalDiagonalPoint (-2) 3 x).toSU6 =
      eval integralSMCharacter x := by
  rw [signed_character_standard _ (physicalDiagonalPoint_last x)]
  exact ten_add_antifive_eq_SM x

open StandardPhysicalSource PhysicalChargeResolvedBridge

/-- All three signed summands carry the same residual charge. -/
def signedSource {A : Type*} (q : A) : FiniteChargedContinuousUnitarySource A :=
  [{ coeff := 1, rep := exteriorTwo, offset := q },
   { coeff := 1, rep := antifundamental, offset := q },
   { coeff := -1, rep := fundamental, offset := q }]

theorem signedSource_character {A : Type*} (q : A)
    (x : UnitAddTorus (Fin 4)) :
    AmbientCharacterBridge.finiteVirtualRestrictedCharacter
        (signedSource q).toVirtual (physicalDiagonalPoint (-2) 3 x) =
      eval integralSMCharacter x := by
  rw [FiniteChargedContinuousUnitarySource.finiteVirtualRestrictedCharacter_toVirtual_eq_sum]
  simpa [signedSource, ActualRestriction.restrictedCharacter, sub_eq_add_neg, add_assoc]
    using signed_character_physical x

/-- Faithfulness recovers the exact integral coefficients of the actual source. -/
theorem signedSource_integralCharacter {A : Type*} (q : A) :
    restrictIntegralCharacter (-2) 3 (signedSource q).ambientLaurentModel.poly =
      integralSMCharacter := by
  apply Fourier.eval_faithful
  intro x
  rw [eval_restrictIntegralCharacter_eq_diagonalEval,
    (signedSource q).ambientLaurentModel.evaluates_character]
  exact signedSource_character q x

theorem summandPhysicalResolvedCharacter_eq_mapDomain
    {A : Type*} [AddCommGroup A] (m n : ℤ) (s : ChargedContinuousUnitarySummand A) :
    summandPhysicalResolvedCharacter m n s =
      Finsupp.mapDomain (fun e => (e, s.offset))
        (restrictIntegralCharacter m n
          (AmbientLaurent.zscale s.coeff s.rep.ambientLaurentModel.poly)) := by
  simp only [summandPhysicalResolvedCharacter, restrictIntegralCharacter,
    ambient_zscale_eq_zsmul, Finsupp.mapDomain_smul, ← Finsupp.mapDomain_comp]
  rfl

/-- Uniform source charges survive physical restriction without being forgotten. -/
theorem uniform_sourcePhysicalResolvedCharacter
    {A : Type*} [AddCommGroup A] (m n : ℤ) (q : A)
    (source : FiniteChargedContinuousUnitarySource A)
    (hCharge : ∀ s ∈ source, s.offset = q) :
    sourcePhysicalResolvedCharacter m n source =
      Finsupp.mapDomain (fun e => (e, q))
        (restrictIntegralCharacter m n source.ambientLaurentModel.poly) := by
  induction source with
  | nil =>
      change 0 = Finsupp.mapDomain (fun e => (e, q)) (restrictIntegralCharacter m n 0)
      simp [restrictIntegralCharacter]
  | cons s source ih =>
      have hs := hCharge s (by simp)
      have htail : ∀ t ∈ source, t.offset = q := fun t ht => hCharge t (by simp [ht])
      change summandPhysicalResolvedCharacter m n s +
          sourcePhysicalResolvedCharacter m n source =
        Finsupp.mapDomain (fun e => (e, q))
          (restrictIntegralCharacter m n
            (AmbientLaurent.zscale s.coeff s.rep.ambientLaurentModel.poly +
              (FiniteChargedContinuousUnitarySource.ambientLaurentModel source).poly))
      rw [summandPhysicalResolvedCharacter_eq_mapDomain, hs, ih htail]
      simp only [restrictIntegralCharacter, Finsupp.mapDomain_add]

/-- A uniform charge assignment, valid also in torsion charge groups. -/
def uniformCharges {A : Type*} (q : A) : StandardBranchProtonObstruction.Charges A :=
  ⟨q, q, q, q, q⟩

theorem smCharge_uniformCharges {A : Type*} (q : A) (i : Fin 15) :
    StandardSMCharacterTarget.smCharge (uniformCharges q) i = q := by
  fin_cases i <;> rfl

theorem mapDomain_integralSMCharacter {A : Type*} (q : A) :
    Finsupp.mapDomain (fun e => (e, q)) integralSMCharacter =
      exactSMWithSingletsResolvedCharacter 1 (uniformCharges q) 0 := by
  classical
  simp only [exactSMWithSingletsResolvedCharacter, singletResolvedCharacter,
    Finsupp.mapDomain_zero, add_zero, integralSMCharacter,
    Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single,
    exactSMResolvedCharacter, physicalSMResolvedKey, smCharge_uniformCharges]

/-- One exact SM generation, with no net singlets, in the common hypercharge character rigidity/standard charge-orbit bridge normal form. -/
theorem signedSource_resolvedCharacter {A : Type*} [AddCommGroup A] (q : A) :
    sourcePhysicalResolvedCharacter (-2) 3 (signedSource q) =
      exactSMWithSingletsResolvedCharacter 1 (uniformCharges q) 0 := by
  rw [uniform_sourcePhysicalResolvedCharacter (-2) 3 q (signedSource q) (by
    intro s hs
    simp only [signedSource, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> rfl)]
  rw [signedSource_integralCharacter, mapDomain_integralSMCharacter]

/-- Local multiplicities, including the absence of other non-singlet index terms. -/
theorem signedSource_coefficientSpectrum {A : Type*} [AddCommGroup A] (q : A) :
    IsExactSMOnlyPhysicalCoefficientSpectrum
      (sourcePhysicalResolvedCharacter (-2) 3 (signedSource q))
      1 (uniformCharges q) 0 :=
  IsExactSMOnlyPhysicalCoefficientSpectrum.of_resolvedCharacter_eq
    (signedSource_resolvedCharacter q)

/-- The existing actual physical-torus target interface, now with a concrete source. -/
theorem signedSource_isSMTargetCharacterEquivalent {A : Type*} (q : A) :
    PhysicalSMTorusTarget.IsSMTargetCharacterEquivalent
      (signedSource q).toVirtual 1 0 (-2) 3 := by
  intro g
  change PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
      (PhysicalSMTorusTarget.restrictVirtual (-2) 3 (signedSource q).toVirtual)
      (Multiplicative.ofAdd g.toAdd) =
    PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
      (PhysicalSMTorusTarget.target 1 0) (Multiplicative.ofAdd g.toAdd)
  rw [PhysicalSMTorusTarget.restrictVirtual_character,
    PhysicalSMTorusTarget.target_character, signedSource_character]
  congr 1
  ext e
  simp [exactSMCharacter, zscale, integralSingletCharacter]

end
end GUT.ConcreteSU6PhysicalTarget
