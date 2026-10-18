import GUT.SU6.SelectionRules.StandardBranch.StandardWeylDualTarget
import GUT.SU6.SelectionRules.StandardBranch.PhysicalChargeResolvedBridge
import Physics.FieldTheory.Mass.UnitaryVirtualRealization

open Math

/-!
# Canonical all-left-handed fields for the standard Weyl mass source

Nonnegative matter multiplicities are actual copies, not signed Dirac
indices. Full charge-sector decomposition and finite orthogonal sums build
the field representation and prove its UV character identification. The
hypercharge branch is fixed to the standard one in this module.
-/

set_option autoImplicit false

namespace GUT.StandardWeylMassSource

noncomputable section

open CompactEmbeddingClassification UnitaryVirtualRealization
open StandardSMCharacterTarget StandardWeylDualTarget InvariantWeylMass
open StandardPhysicalSource (ChargedContinuousUnitarySummand FiniteChargedContinuousUnitarySource)
open StandardPhysicalCharacterBridge (chargedProductRho combinedGaugeHom sourceProductRepresentation)
open StandardBlockGaugeCancellation (OrdinaryAbelianSource)
open PhysicalRestrictionBridge (FiniteVirtualGroupRepresentation)
open PhysicalChargeResolvedBridge (ordinaryChargedSource)
open StandardBranchProtonObstruction (Charges SU5OrbitCompatible protonFirst protonSecond)

variable {H : Type*} [CommGroup H]

/-- Each scalar residual charge preserves the Hermitian form of its actual
SU(6) sector. No gauge twist is introduced. -/
def sectorUnitaryRepresentation (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    ActualUnitaryGroupRepresentation (CombinedGroup H) where
  V := s.rep.V
  rho := chargedProductRho 1 s
  unitary := by
    intro g v w
    change inner ℂ
      (((s.offset.toMul g.2 : Circle) : ℂ) • s.rep.rho (combinedGaugeHom 1 g) v)
      (((s.offset.toMul g.2 : Circle) : ℂ) • s.rep.rho (combinedGaugeHom 1 g) w) = _
    rw [inner_smul_left, inner_smul_right, ← Circle.coe_inv_eq_conj]
    simp
    exact s.rep.unitary (combinedGaugeHom 1 g) v w

def unitarySource (source : FiniteChargedContinuousUnitarySource (ChargeLabel H)) :
    FiniteUnitaryVirtualRepresentation (CombinedGroup H) :=
  source.map fun s => { coeff := s.coeff, rep := sectorUnitaryRepresentation s }

theorem unitarySource_toFiniteVirtual
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H)) :
    (unitarySource source).toFiniteVirtual = sourceProductRepresentation 1 source := by
  induction source with
  | nil => rfl
  | cons s source ih =>
      change _ :: (unitarySource source).toFiniteVirtual =
        _ :: sourceProductRepresentation 1 source
      rw [ih]
      rfl

/-- The canonical finite orthogonal sum of all left-handed charge sectors. -/
def fields (source : FiniteChargedContinuousUnitarySource (ChargeLabel H)) :
    ActualUnitaryGroupRepresentation (CombinedGroup H) :=
  (unitarySource source).positive

/-- The source identification is derived from multiplicities, not assumed
as a character-model field. Negative virtual multiplicities are not allowed. -/
theorem fields_character
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H))
    (hcoeff : ∀ s ∈ source, 0 ≤ s.coeff) (g : CombinedGroup H) :
    (fields source).rho.character g =
      FiniteVirtualGroupRepresentation.character (sourceProductRepresentation 1 source) g := by
  rw [fields, FiniteUnitaryVirtualRepresentation.positive_character_of_nonnegative]
  · rw [unitarySource_toFiniteVirtual]
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact hcoeff t ht

/-- Refining actual matter into full residual-character sectors preserves
each nonnegative multiplicity. -/
theorem ordinaryChargedSource_nonnegative (matter : OrdinaryAbelianSource H)
    (hcoeff : ∀ s ∈ matter, 0 ≤ s.coeff) :
    ∀ s ∈ ordinaryChargedSource matter, 0 ≤ s.coeff := by
  revert hcoeff
  induction matter with
  | nil => simp [ordinaryChargedSource,
      StandardBlockGaugeCancellation.OrdinaryAbelianSource.toCommonGaugeSource,
      StandardBlockGaugeCancellation.CommonGaugeSource.toChargedSource]
  | cons s matter ih =>
      intro hcoeff t ht
      change t ∈ s.toCommonGaugeSummand.toChargedSource ++ ordinaryChargedSource matter at ht
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
        exact hcoeff s (by simp)
      · exact ih (fun u hu => hcoeff u (List.mem_cons_of_mem s hu)) t ht

def ordinaryFields (matter : OrdinaryAbelianSource H) :
    ActualUnitaryGroupRepresentation (CombinedGroup H) := fields (ordinaryChargedSource matter)

theorem ordinaryFields_character (matter : OrdinaryAbelianSource H)
    (hcoeff : ∀ s ∈ matter, 0 ≤ s.coeff) (g : CombinedGroup H) :
    (ordinaryFields matter).rho.character g =
      FiniteVirtualGroupRepresentation.character
        (sourceProductRepresentation 1 (ordinaryChargedSource matter)) g :=
  fields_character _ (ordinaryChargedSource_nonnegative matter hcoeff) g

/-- Standard-branch standard charge-orbit bridge -> Abelian proton-operator neutrality for general symmetric masses on the canonical
actual fields. There is no `hSource` assumption. The radical's dual SM target
is still the explicit infrared applicability condition. -/
theorem ordinaryFields_proton_functionals_eq_zero
    (matter : OrdinaryAbelianSource H) (hcoeff : ∀ s ∈ matter, 0 ≤ s.coeff)
    (B : SymmetricMass (ordinaryFields matter).rho)
    (n : ℤ) (hn : n ≠ 0) (k : Charges (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
    (hLight : FiniteVirtualGroupRepresentation.CharacterEquivalent (lightDualIndex B)
      (ofCharacter (chiralDifference (exactSMWithSingletsResolvedCharacter n k s)))) :
    protonFirst k = 0 ∧ protonSecond k = 0 :=
  chargedSource_proton_functionals_eq_zero_of_mass_dual_target
    B (ordinaryFields matter).unitary (ordinaryChargedSource matter)
    (fun x h => ordinaryFields_character matter hcoeff (Multiplicative.ofAdd x, h))
    n hn k s hLight

/-- A standard-branch all-left-handed mass model. Matter multiplicities are
nonnegative, while an arbitrary invariant symmetric form allows Majorana
terms and zero mass. No UV character-identification field is requested. -/
structure StandardWeylModel (H : Type*) [CommGroup H] where
  matter : OrdinaryAbelianSource H
  nonnegative : ∀ s ∈ matter, 0 ≤ s.coeff
  mass : SymmetricMass (ordinaryFields matter).rho
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  lightTarget : FiniteVirtualGroupRepresentation.CharacterEquivalent (lightDualIndex mass)
    (ofCharacter (chiralDifference
      (exactSMWithSingletsResolvedCharacter generations charges singlets)))

theorem StandardWeylModel.proton_functionals_eq_zero (M : StandardWeylModel H) :
    protonFirst M.charges = 0 ∧ protonSecond M.charges = 0 :=
  ordinaryFields_proton_functionals_eq_zero M.matter M.nonnegative M.mass
    M.generations M.generations_ne M.charges M.singlets M.lightTarget

end

end GUT.StandardWeylMassSource
