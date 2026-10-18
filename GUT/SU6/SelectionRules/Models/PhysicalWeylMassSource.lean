import GUT.SU6.SelectionRules.StandardBranch.PhysicalWeylChargeBridge
import GUT.SU6.SelectionRules.Models.PhysicalMassSpectrumBridge
import GUT.SU6.SelectionRules.StandardBranch.StandardWeylMassSource

open Math

/-!
# Canonical Weyl fields and symmetric masses at arbitrary cocharacters

Nonnegative actual matter coefficients build all-left-handed fields. Their
trace is the physical resolved evaluator at (m,n), derived from full charge
sectors. Conservation of the radical's dual index supplies the single hypercharge character rigidity/standard charge-orbit bridge
target. No UV character model, standard pair, or charge equality is a field
of the model.
-/

set_option autoImplicit false

namespace GUT.PhysicalWeylMassSource

noncomputable section

open PhysicalChargeResolvedBridge PhysicalChargeResolvedEvaluation PhysicalMassSpectrumBridge
open PhysicalRestrictionBridge PhysicalWeylMomentBridge
open PhysicalChargedCharacterBridge
  (sourceUnitaryRepresentation sourceUnitaryRepresentation_toFiniteVirtual sourceProductRepresentation_character)
open StandardPhysicalSource StandardBranchProtonObstruction InvariantWeylMass
open StandardBlockGaugeCancellation (OrdinaryAbelianSource)
open UnitaryVirtualRealization

variable {H : Type*} [CommGroup H]

theorem sourceUnitary_nonnegative (m n : ℤ)
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H))
    (hc : ∀ s ∈ source, 0 ≤ s.coeff) :
    ∀ s ∈ sourceUnitaryRepresentation m n source, 0 ≤ s.coeff := by
  induction source with
  | nil => simp [sourceUnitaryRepresentation]
  | cons s source ih =>
      intro t ht
      change t ∈ _ :: sourceUnitaryRepresentation m n source at ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hc s (by simp)
      · exact ih (fun u hu => hc u (List.mem_cons_of_mem s hu)) t ht

theorem fields_character (m n : ℤ) (matter : OrdinaryAbelianSource H)
    (hc : ∀ s ∈ matter, 0 ≤ s.coeff) (x : UnitAddTorus (Fin 4)) (h : H) :
    (ordinaryPositiveRepresentation m n matter).rho.character (Multiplicative.ofAdd x, h) =
      eval (ordinaryPhysicalResolvedCharacter m n matter) x h := by
  unfold ordinaryPositiveRepresentation ordinaryUnitaryVirtualSource
  rw [FiniteUnitaryVirtualRepresentation.positive_character_of_nonnegative]
  · rw [sourceUnitaryRepresentation_toFiniteVirtual]
    exact sourceProductRepresentation_character m n (ordinaryChargedSource matter) x h
  · exact sourceUnitary_nonnegative m n _
      (StandardWeylMassSource.ordinaryChargedSource_nonnegative matter hc)

theorem keyMonoidHom_neg (key : PhysicalResolvedKey (ChargeLabel H)) (g : CombinedGroup H) :
    keyMonoidHom (-key) g = keyMonoidHom key g⁻¹ := by
  rcases g with ⟨x, h⟩
  change UnitAddTorus.mFourier (-key.1) x.toAdd * (((-key.2).toMul h : Circle) : ℂ) =
    UnitAddTorus.mFourier key.1 (-x.toAdd) * ((key.2.toMul h⁻¹ : Circle) : ℂ)
  congr 1
  · simp [UnitAddTorus.mFourier, neg_smul]
  · rw [map_inv]; rfl

theorem eval_dual (p : PhysicalResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) : eval (dual p) x h = eval p (-x) h⁻¹ := by
  unfold eval dual
  rw [Finsupp.sum_mapDomain_index]
  · apply Finsupp.sum_congr
    intro key _
    rw [keyMonoidHom_neg]
    rfl
  · simp
  · intros; push_cast; ring

theorem eval_chiralDifference (p : PhysicalResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (chiralDifference p) x h = eval p x h - eval p (-x) h⁻¹ := by
  change PhysicalChargeResolvedEvaluation.evalAddHom x h (p - dual p) = _
  rw [map_sub]
  exact congrArg (fun z => eval p x h - z) (eval_dual p x h)

def HasDualSMTarget {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {rho : Representation ℂ (CombinedGroup H) E}
    (B : SymmetricMass rho) (generations : ℤ) (charges : Charges (ChargeLabel H))
    (singlets : ChargeLabel H →₀ ℤ) : Prop :=
  FiniteVirtualGroupRepresentation.CharacterEquivalent (lightDualIndex B)
    (ofCharacter (chiralDifference
      (exactSMWithSingletsResolvedCharacter generations charges singlets)))

theorem eval_embedStandardCharacter
    (p : StandardAbelianCharge.ResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (embedStandardCharacter p) x h = StandardSMCharacterTarget.eval p x h := by
  unfold eval embedStandardCharacter
  rw [Finsupp.sum_mapDomain_index]
  · rfl
  · simp
  · intros; push_cast; ring

theorem HasDualSMTarget.standard {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {rho : Representation ℂ (CombinedGroup H) E}
    {B : SymmetricMass rho} {generations : ℤ} {charges : Charges (ChargeLabel H)}
    {singlets : ChargeLabel H →₀ ℤ} (ht : HasDualSMTarget B generations charges singlets) :
    FiniteVirtualGroupRepresentation.CharacterEquivalent (lightDualIndex B)
      (StandardSMCharacterTarget.ofCharacter (StandardWeylDualTarget.chiralDifference
        (StandardSMCharacterTarget.exactSMWithSingletsResolvedCharacter generations charges singlets))) := by
  intro g
  have he := ht g
  change _ = FiniteVirtualGroupRepresentation.character (ofCharacter _) (Multiplicative.ofAdd g.1.toAdd, g.2) at he
  rw [character_ofCharacter, exactSMWithSingletsResolvedCharacter_standard,
    ← PhysicalWeylChargeBridge.embedStandardCharacter_chiralDifference,
    eval_embedStandardCharacter] at he
  exact he.trans (StandardSMCharacterTarget.character_ofCharacter _ g.1.toAdd g.2).symm

theorem dualResolved_of_lightTarget (m n : ℤ) (matter : OrdinaryAbelianSource H)
    (hc : ∀ s ∈ matter, 0 ≤ s.coeff)
    (B : SymmetricMass (ordinaryPositiveRepresentation m n matter).rho)
    (generations : ℤ) (charges : Charges (ChargeLabel H)) (singlets : ChargeLabel H →₀ ℤ)
    (ht : HasDualSMTarget B generations charges singlets) :
    chiralDifference (ordinaryPhysicalResolvedCharacter m n matter) =
      chiralDifference (exactSMWithSingletsResolvedCharacter generations charges singlets) := by
  apply eval_faithful
  intro x h
  rw [eval_chiralDifference, ← fields_character m n matter hc,
    ← fields_character m n matter hc]
  have hu := ultravioletDualIndex_characterEquivalent_of_lightDualIndex B
    (ordinaryPositiveRepresentation m n matter).unitary _ ht (Multiplicative.ofAdd x, h)
  simpa only [dualIndex_character, Representation.char_dual, character_ofCharacter,
    Prod.inv_mk, ofAdd_neg] using hu

/-- The reverse direction is useful for concrete constructors: every
invariant mass preserves the same proved ultraviolet dual target. -/
theorem lightTarget_of_dualResolved (m n : ℤ) (matter : OrdinaryAbelianSource H)
    (hc : ∀ s ∈ matter, 0 ≤ s.coeff)
    (B : SymmetricMass (ordinaryPositiveRepresentation m n matter).rho)
    (generations : ℤ) (charges : Charges (ChargeLabel H)) (singlets : ChargeLabel H →₀ ℤ)
    (ht : chiralDifference (ordinaryPhysicalResolvedCharacter m n matter) =
      chiralDifference (exactSMWithSingletsResolvedCharacter generations charges singlets)) :
    HasDualSMTarget B generations charges singlets := by
  intro g
  have he := lightDualIndex_characterEquivalent_ultravioletDualIndex B
    (ordinaryPositiveRepresentation m n matter).unitary g
  rw [dualIndex_character, Representation.char_dual] at he
  rw [he]
  change _ = FiniteVirtualGroupRepresentation.character (ofCharacter _) (Multiplicative.ofAdd g.1.toAdd, g.2)
  rw [character_ofCharacter, ← ht, eval_chiralDifference]
  exact congrArg₂ (fun a b : ℂ => a - b)
    (fields_character m n matter hc g.1.toAdd g.2)
    (fields_character m n matter hc (-g.1.toAdd) g.2⁻¹)

structure PhysicalWeylModel (H : Type*) [CommGroup H] where
  colorExponent : ℤ
  weakExponent : ℤ
  matter : OrdinaryAbelianSource H
  nonnegative : ∀ s ∈ matter, 0 ≤ s.coeff
  mass : SymmetricMass (ordinaryPositiveRepresentation colorExponent weakExponent matter).rho
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  lightTarget : HasDualSMTarget mass generations charges singlets

namespace PhysicalWeylModel

variable (M : PhysicalWeylModel H)

theorem dualResolved :
    chiralDifference (ordinaryPhysicalResolvedCharacter M.colorExponent M.weakExponent M.matter) =
      chiralDifference (exactSMWithSingletsResolvedCharacter M.generations M.charges M.singlets) :=
  dualResolved_of_lightTarget M.colorExponent M.weakExponent M.matter M.nonnegative M.mass
    M.generations M.charges M.singlets M.lightTarget

theorem hypercharge_eq_standard : M.colorExponent = -2 ∧ M.weakExponent = 3 :=
  PhysicalWeylChargeBridge.eq_standard_of_dualResolved (ordinaryChargedSource M.matter)
    M.generations M.charges M.singlets M.colorExponent M.weakExponent M.generations_ne M.dualResolved

theorem su5OrbitCompatible : SU5OrbitCompatible M.charges :=
  PhysicalWeylChargeBridge.su5OrbitCompatible_of_dualResolved (ordinaryChargedSource M.matter)
    M.generations M.charges M.singlets M.colorExponent M.weakExponent M.generations_ne M.dualResolved

theorem proton_functionals_eq_zero : protonFirst M.charges = 0 ∧ protonSecond M.charges = 0 :=
  proton_functionals_eq_zero_of_su5OrbitCompatible M.charges M.su5OrbitCompatible

end PhysicalWeylModel

end

end GUT.PhysicalWeylMassSource
