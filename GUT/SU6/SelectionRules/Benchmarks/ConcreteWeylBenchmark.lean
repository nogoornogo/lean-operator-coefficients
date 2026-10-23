import GUT.SU6.SelectionRules.StandardBranch.StandardWeylMassSource
import GUT.SU6.SelectionRules.Benchmarks.ConcreteDiracBenchmark

open Physics

open Math

/-!
# A non-vacuous standard Weyl mass model

Actual left-handed matter is `15 + 2 bar6`, with nonnegative multiplicities
and neutral residual action. Its dual index is that of one SM generation.
The explicit mass is zero; extra vectorlike and self-dual zero modes remain.
-/

set_option autoImplicit false

namespace GUT.ConcreteWeylBenchmark

noncomputable section

open ConcreteSU6Representations ConcreteSU6PhysicalTarget
open ConcreteDiracBenchmark (neutralAction chargedSectorSource_neutral)
open StandardWeylMassSource StandardWeylDualTarget InvariantWeylMass
open StandardBlockGaugeCancellation (OrdinaryAbelianSource OrdinaryAbelianSummand)
open StandardSMCharacterTarget
open StandardPhysicalSource (FiniteChargedContinuousUnitarySource)
open StandardPhysicalCharacterBridge
  (chargedProductRho combinedGaugeHom sourceProductRepresentation)
open PhysicalChargeResolvedBridge (ordinaryChargedSource ordinaryChargedSource_restrictedCharacter_eq)
open PhysicalRestrictionBridge (FiniteVirtualGroupRepresentation)

variable {H : Type*} [CommGroup H]

def matter (H : Type*) [CommGroup H] : OrdinaryAbelianSource H :=
  [{ coeff := 1, rep := exteriorTwo, action := neutralAction exteriorTwo },
   { coeff := 2, rep := antifundamental, action := neutralAction antifundamental }]

theorem matter_nonnegative : ∀ s ∈ matter H, 0 ≤ s.coeff := by
  intro s hs
  simp only [matter, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> norm_num

theorem chargedSource_neutral :
    ∀ s ∈ ordinaryChargedSource (matter H), s.offset = 0 := by
  have hs (s : OrdinaryAbelianSummand H) (ha : s.action.rho = 1) :
      ∀ t ∈ s.toCommonGaugeSummand.toChargedSource, t.offset = 0 := by
    apply chargedSectorSource_neutral
    change s.toCommonGaugeSummand.twisted.externalRepresentation = 1
    rw [OrdinaryAbelianSummand.toCommonGaugeSummand_externalRepresentation, ha]
    rfl
  intro s hmem
  change s ∈ _ ++ (_ ++ []) at hmem
  simp only [List.mem_append, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h
  all_goals exact hs _ rfl s h

/-- Neutral charge-sector refinement does not change the actual torus trace. -/
theorem source_character_neutral
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H))
    (hzero : ∀ s ∈ source, s.offset = 0)
    (x : UnitAddTorus (Fin 4)) (h : H) :
    FiniteVirtualGroupRepresentation.character (sourceProductRepresentation 1 source)
        (Multiplicative.ofAdd x, h) =
      AmbientCharacterBridge.finiteVirtualRestrictedCharacter source.toVirtual
        (PhysicalTorusCharacterBridge.physicalDiagonalPoint (-2) 3 x) := by
  revert hzero
  induction source with
  | nil => intro _; rfl
  | cons s source ih =>
      intro hzero
      have hs := hzero s (by simp)
      have hrho : chargedProductRho (1 : H →* Circle) s =
          s.rep.rho.comp (combinedGaugeHom 1) := by
        apply MonoidHom.ext
        intro g
        apply LinearMap.ext
        intro v
        simp [chargedProductRho, hs]
      change (s.coeff : ℂ) * (chargedProductRho 1 s).character
          (Multiplicative.ofAdd x, h) + _ =
        (s.coeff : ℂ) * s.rep.rho.character
          (PhysicalTorusCharacterBridge.physicalDiagonalPoint (-2) 3 x).toSU6 + _
      rw [ih (fun t ht => hzero t (List.mem_cons_of_mem s ht)), hrho]
      congr 2
      change s.rep.rho.character (combinedGaugeHom 1 (Multiplicative.ofAdd x, h)) = _
      simp [PhysicalSMTorusTarget.embedding_ofAdd]

theorem fields_character (x : UnitAddTorus (Fin 4)) (h : H) :
    (ordinaryFields (matter H)).rho.character (Multiplicative.ofAdd x, h) =
      exteriorTwo.rho.character (PhysicalSMTorusTarget.embedding (-2) 3 (Multiplicative.ofAdd x)) +
        2 * antifundamental.rho.character
          (PhysicalSMTorusTarget.embedding (-2) 3 (Multiplicative.ofAdd x)) := by
  rw [ordinaryFields_character _ matter_nonnegative,
    source_character_neutral _ chargedSource_neutral,
    ordinaryChargedSource_restrictedCharacter_eq, PhysicalSMTorusTarget.embedding_ofAdd]
  simp [matter, OrdinaryAbelianSource.toFiniteVirtual,
    OrdinaryAbelianSummand.toVirtualSummand,
    ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation.toActualRepresentation,
    AmbientCharacterBridge.finiteVirtualRestrictedCharacter,
    AmbientCharacterBridge.summandRestrictedCharacter,
    AmbientCharacterBridge.actualRestrictedCharacter, ActualRestriction.restrictedCharacter]

theorem antifundamental_character_eq_inverse (g : ActualRestriction.SU6) :
    antifundamental.rho.character g = fundamental.rho.character g⁻¹ := by
  have he := congrFun (Representation.char_iso
    (ContinuousUnitaryConstructions.ContinuousUnitarySU6Representation.dualEquiv
      fundamental)) g
  change fundamental.rho.dual.character g = antifundamental.rho.character g at he
  rw [Representation.char_dual] at he
  exact he.symm

/-- The neutral charge-resolved target evaluates to the existing physical
SM character. No spectrum assumption enters this calculation. -/
theorem neutral_target_eval (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0) x h =
      PhysicalTorusCharacterBridge.eval PhysicalTorusCharacterBridge.integralSMCharacter x := by
  classical
  rw [ConcreteSU6PhysicalTarget.eval_integralSMCharacter]
  simp only [exactSMWithSingletsResolvedCharacter, singletResolvedCharacter,
    Finsupp.mapDomain_zero, add_zero, exactSMResolvedCharacter, eval]
  rw [← Finsupp.sum_finsetSum_index]
  · simp [keyMonoidHom_apply, smResolvedKey, smCharge_uniformCharges,
      standardExponent_eq_restrictExponent_rawReducedWeight, restrictExponent_smReducedWeight]
  · intro key
    simp
  · intro key a b
    simp [add_mul]

theorem signed_target_eval (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0) x h =
      exteriorTwo.rho.character (PhysicalSMTorusTarget.embedding (-2) 3 (Multiplicative.ofAdd x)) +
        antifundamental.rho.character (PhysicalSMTorusTarget.embedding (-2) 3 (Multiplicative.ofAdd x)) -
        fundamental.rho.character (PhysicalSMTorusTarget.embedding (-2) 3 (Multiplicative.ofAdd x)) := by
  rw [neutral_target_eval, PhysicalSMTorusTarget.embedding_ofAdd]
  exact (signed_character_physical x).symm

/-- The actual all-left-handed field character differs from the signed
target by `6 + bar6`, whose dual chiral difference vanishes. -/
theorem fields_dual_character (x : UnitAddTorus (Fin 4)) (h : H) :
    (ordinaryFields (matter H)).rho.character (Multiplicative.ofAdd x, h) -
        (ordinaryFields (matter H)).rho.dual.character (Multiplicative.ofAdd x, h) =
      eval (chiralDifference
        (exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0)) x h := by
  rw [Representation.char_dual, eval_chiralDifference]
  change (ordinaryFields (matter H)).rho.character (Multiplicative.ofAdd x, h) -
      (ordinaryFields (matter H)).rho.character (Multiplicative.ofAdd (-x), h⁻¹) = _
  rw [fields_character, fields_character, signed_target_eval, signed_target_eval]
  have hinv : PhysicalSMTorusTarget.embedding (-2) 3 (Multiplicative.ofAdd (-x)) =
      (PhysicalSMTorusTarget.embedding (-2) 3 (Multiplicative.ofAdd x))⁻¹ :=
    map_inv _ _
  rw [hinv, antifundamental_character_eq_inverse,
    antifundamental_character_eq_inverse, inv_inv]
  ring

/-- Every invariant symmetric mass on this matter preserves the proved
one-generation dual target, regardless of its rank. -/
theorem mass_hasDualSMTarget (B : SymmetricMass (ordinaryFields (matter H)).rho) :
    FiniteVirtualGroupRepresentation.CharacterEquivalent (lightDualIndex B)
      (ofCharacter (chiralDifference
        (exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0))) := by
  intro g
  change (dualIndex B.radical.toRepresentation).character (Multiplicative.ofAdd g.1.toAdd, g.2) = _
  rw [dualIndex_character, radical_dual_character_eq B (ordinaryFields (matter H)).unitary]
  rw [fields_dual_character]
  exact (character_ofCharacter _ g.1.toAdd g.2).symm

def model (H : Type*) [CommGroup H] : StandardWeylModel H where
  matter := matter H
  nonnegative := matter_nonnegative
  mass := SymmetricMass.zero _
  generations := 1
  generations_ne := by norm_num
  charges := uniformCharges 0
  singlets := 0
  lightTarget := mass_hasDualSMTarget _

theorem model_mass_zero : (model H).mass.form = 0 := rfl

theorem fields_finrank : Module.finrank ℂ (ordinaryFields (matter H)).V = 27 := by
  have h := fields_character (H := H) 0 1
  simp only [show Multiplicative.ofAdd (0 : UnitAddTorus (Fin 4)) =
    (1 : CompactTorus) from rfl, map_one] at h
  change (ordinaryFields (matter H)).rho.character 1 =
    exteriorTwo.rho.character 1 + 2 * antifundamental.rho.character 1 at h
  rw [Representation.char_one, Representation.char_one, Representation.char_one,
    exteriorTwo_finrank, antifundamental_finrank] at h
  have hc : (Module.finrank ℂ (ordinaryFields (matter H)).V : ℂ) = 27 := by
    norm_num at h ⊢
    exact h
  exact_mod_cast hc

private theorem zero_mass_radical_finrank
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    Module.finrank ℂ (SymmetricMass.zero rho).radical.toSubmodule = Module.finrank ℂ V := by
  rw [SymmetricMass.radical_zero]
  simp

set_option maxHeartbeats 800000 in
/-- The witness has all twenty-seven actual field modes at zero mass. It
does not identify a pure fifteen-dimensional SM zero-mode spectrum. -/
theorem model_radical_finrank :
    Module.finrank ℂ (model H).mass.radical.toSubmodule = 27 :=
  (zero_mass_radical_finrank (ordinaryFields (matter H)).rho).trans fields_finrank

theorem exists_one_generation_model (H : Type*) [CommGroup H] :
    ∃ M : StandardWeylModel H, M.generations = 1 := ⟨model H, rfl⟩

end

end GUT.ConcreteWeylBenchmark
