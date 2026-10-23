import GUT.SU6.SelectionRules.StandardBranch.ScalarResidualSource
import GUT.SU6.SelectionRules.Models.ContinuousProfileModel
import GUT.SU6.SelectionRules.Benchmarks.ConcreteWeylBenchmark

open Physics

open Math

/-!
# An actual two-charge continuous SU(6) model

Two copies of `15 + 2 bar6` carry the trivial and a self-inverse residual
character. Their dual target is derived from actual traces. The zero mass
retains vectorlike modes; a pure thirty-dimensional radical is not claimed.
-/

set_option autoImplicit false

namespace GUT.NonuniformProfileModel

noncomputable section

open ConcreteSU6Representations StandardBlockGaugeCancellation
open ConcreteSU6PhysicalTarget (uniformCharges smCharge_uniformCharges)
open PhysicalMassSpectrumBridge InvariantWeylMass StandardSMCharacterTarget
open StandardWeylDualTarget StandardAbelianCharge FiniteChargeProfiles
open PhysicalRestrictionBridge (FiniteVirtualGroupRepresentation)

variable {H : Type*} [CommGroup H]

def chargedMatter (chi : H →* Circle) : OrdinaryAbelianSource H :=
  [{ coeff := 1, rep := exteriorTwo, action := ScalarResidualSource.action exteriorTwo chi },
   { coeff := 2, rep := antifundamental, action := ScalarResidualSource.action antifundamental chi }]

theorem chargedMatter_nonnegative (chi : H →* Circle) :
    ∀ s ∈ chargedMatter chi, 0 ≤ s.coeff := by
  intro s hs
  simp only [chargedMatter, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> norm_num

def matter (chi : H →* Circle) : OrdinaryAbelianSource H :=
  chargedMatter 1 ++ chargedMatter chi

theorem matter_nonnegative (chi : H →* Circle) : ∀ s ∈ matter chi, 0 ≤ s.coeff := by
  intro s hs
  exact (List.mem_append.mp hs).elim
    (chargedMatter_nonnegative 1 s) (chargedMatter_nonnegative chi s)

def family (q : ChargeLabel H) : Family (ChargeLabel H) where
  profiles := uniformCharges (Finsupp.single 0 1 + Finsupp.single q 1)
  generations := 2
  positive := by decide
  totals := by constructor <;> simp [uniformCharges]

theorem target_eq (q : ChargeLabel H) :
    targetWithSinglets (family q).profiles 0 =
      exactSMWithSingletsResolvedCharacter 1 (uniformCharges 0) 0 +
        exactSMWithSingletsResolvedCharacter 1 (uniformCharges q) 0 := by
  classical
  have hi : integral (Finsupp.single (0 : ChargeLabel H) 1 + Finsupp.single q 1) =
      Finsupp.single 0 1 + Finsupp.single q 1 := by
    ext r
    simp [integral, Finsupp.single_apply]
  simp only [FiniteChargeProfiles.targetWithSinglets, family, FiniteChargeProfiles.target,
    smCharge_uniformCharges, atWeight, hi,
    Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finset.sum_add_distrib,
    singletResolvedCharacter, Finsupp.mapDomain_zero, add_zero,
    exactSMWithSingletsResolvedCharacter, exactSMResolvedCharacter, smResolvedKey,
    smCharge_uniformCharges]

theorem eval_add (p r : ResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (p + r) x h = eval p x h + eval r x h := by
  exact Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring)

theorem uniform_target_eval (q : ChargeLabel H) (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (exactSMWithSingletsResolvedCharacter 1 (uniformCharges q) 0) x h =
      (q.toMul h : ℂ) * eval
        (exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0) x h := by
  classical
  simp only [exactSMWithSingletsResolvedCharacter, singletResolvedCharacter,
    Finsupp.mapDomain_zero, add_zero, exactSMResolvedCharacter, eval]
  rw [← Finsupp.sum_finsetSum_index, ← Finsupp.sum_finsetSum_index, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro i _
    simp [keyMonoidHom_apply, smResolvedKey, smCharge_uniformCharges, mul_comm]
  all_goals (intros; simp [add_mul])

theorem target_eval (q : ChargeLabel H) (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (targetWithSinglets (family q).profiles 0) x h =
      (1 + (q.toMul h : ℂ)) * eval
        (exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0) x h := by
  rw [target_eq, eval_add, uniform_target_eval q]
  ring

theorem charged_fields_character (chi : H →* Circle) (m n : ℤ)
    (x : UnitAddTorus (Fin 4)) (h : H) :
    (ordinaryPositiveRepresentation m n (chargedMatter chi)).rho.character
        (Multiplicative.ofAdd x, h) =
      (chi h : ℂ) * (exteriorTwo.rho.character
        (PhysicalSMTorusTarget.embedding m n (Multiplicative.ofAdd x)) +
        2 * antifundamental.rho.character
          (PhysicalSMTorusTarget.embedding m n (Multiplicative.ofAdd x))) := by
  rw [ScalarResidualSource.fields_character_uniform m n _ (chargedMatter_nonnegative chi) chi]
  · simp [chargedMatter, OrdinaryAbelianSource.toFiniteVirtual,
      OrdinaryAbelianSummand.toVirtualSummand,
      ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation.toActualRepresentation,
      AmbientCharacterBridge.finiteVirtualRestrictedCharacter,
      AmbientCharacterBridge.summandRestrictedCharacter,
      AmbientCharacterBridge.actualRestrictedCharacter, ActualRestriction.restrictedCharacter,
      PhysicalSMTorusTarget.embedding_ofAdd]
  · intro s hs h v
    simp only [chargedMatter, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> rfl

theorem fields_character (chi : H →* Circle) (m n : ℤ)
    (x : UnitAddTorus (Fin 4)) (h : H) :
    (ordinaryPositiveRepresentation m n (matter chi)).rho.character
        (Multiplicative.ofAdd x, h) =
      (1 + (chi h : ℂ)) * (exteriorTwo.rho.character
        (PhysicalSMTorusTarget.embedding m n (Multiplicative.ofAdd x)) +
        2 * antifundamental.rho.character
          (PhysicalSMTorusTarget.embedding m n (Multiplicative.ofAdd x))) := by
  rw [matter, ScalarResidualSource.fields_character_append _ _ _ _
    (chargedMatter_nonnegative 1) (chargedMatter_nonnegative chi),
    charged_fields_character, charged_fields_character]
  simp only [MonoidHom.one_apply, Circle.coe_one]
  ring

theorem fields_dual_character (chi : H →* Circle) (hi : ∀ h, chi h⁻¹ = chi h)
    (x : UnitAddTorus (Fin 4)) (h : H) :
    (ordinaryPositiveRepresentation (-2) 3 (matter chi)).rho.character
        (Multiplicative.ofAdd x, h) -
      (ordinaryPositiveRepresentation (-2) 3 (matter chi)).rho.dual.character
        (Multiplicative.ofAdd x, h) =
      eval (chiralDifference (targetWithSinglets (family (Additive.ofMul chi)).profiles 0)) x h := by
  rw [Representation.char_dual, eval_chiralDifference]
  change (ordinaryPositiveRepresentation (-2) 3 (matter chi)).rho.character
      (Multiplicative.ofAdd x, h) -
    (ordinaryPositiveRepresentation (-2) 3 (matter chi)).rho.character
      (Multiplicative.ofAdd (-x), h⁻¹) = _
  rw [fields_character, fields_character, target_eval, target_eval]
  change _ = (1 + (chi h : ℂ)) * _ - (1 + (chi h⁻¹ : ℂ)) * _
  rw [hi, ConcreteWeylBenchmark.signed_target_eval, ConcreteWeylBenchmark.signed_target_eval]
  have hinv : PhysicalSMTorusTarget.embedding (-2) 3 (Multiplicative.ofAdd (-x)) =
      (PhysicalSMTorusTarget.embedding (-2) 3 (Multiplicative.ofAdd x))⁻¹ := map_inv _ _
  rw [hinv, ConcreteWeylBenchmark.antifundamental_character_eq_inverse,
    ConcreteWeylBenchmark.antifundamental_character_eq_inverse, inv_inv]
  ring

theorem mass_hasTarget (chi : H →* Circle) (hi : ∀ h, chi h⁻¹ = chi h)
    (B : SymmetricMass (ordinaryPositiveRepresentation (-2) 3 (matter chi)).rho) :
    ProfileZeroModeSupport.HasTarget _ B (family (Additive.ofMul chi)).profiles 0 := by
  intro g
  change (dualIndex B.radical.toRepresentation).character (Multiplicative.ofAdd g.1.toAdd, g.2) = _
  rw [dualIndex_character, radical_dual_character_eq B
    (ordinaryPositiveRepresentation (-2) 3 (matter chi)).unitary,
    fields_dual_character chi hi]
  exact (character_ofCharacter _ g.1.toAdd g.2).symm

def model (chi : H →* Circle) (hi : ∀ h, chi h⁻¹ = chi h) : ContinuousProfileModel.Model H where
  geometry := ConcreteStandardGeometry.geometry
  matter := matter chi
  nonnegative := matter_nonnegative chi
  mass := SymmetricMass.zero _
  profile := family (Additive.ofMul chi)
  singlets := 0
  lightTarget := by
    rw [ConcreteStandardGeometry.hyperchargePair_eq_standard]
    exact mass_hasTarget chi hi _

theorem fields_finrank (chi : H →* Circle) (m n : ℤ) :
    Module.finrank ℂ (ordinaryPositiveRepresentation m n (matter chi)).V = 54 := by
  have he := fields_character chi m n 0 1
  simp only [show Multiplicative.ofAdd (0 : UnitAddTorus (Fin 4)) =
    (1 : CompactTorus) from rfl, map_one] at he
  change (ordinaryPositiveRepresentation m n (matter chi)).rho.character 1 =
    (1 + (1 : Circle).val) * (exteriorTwo.rho.character 1 + 2 * antifundamental.rho.character 1) at he
  rw [Representation.char_one, Representation.char_one, Representation.char_one,
    exteriorTwo_finrank, antifundamental_finrank] at he
  norm_num at he
  exact_mod_cast he

@[simp] theorem model_mass_zero (chi : H →* Circle) (hi : ∀ h, chi h⁻¹ = chi h) :
    (model chi hi).mass.form = 0 := rfl

private theorem zero_mass_radical_finrank
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    Module.finrank ℂ (SymmetricMass.zero rho).radical.toSubmodule = Module.finrank ℂ V := by
  rw [SymmetricMass.radical_zero]
  simp

theorem model_radical_finrank (chi : H →* Circle) (hi : ∀ h, chi h⁻¹ = chi h) :
    Module.finrank ℂ (model chi hi).mass.radical.toSubmodule = 54 :=
  (zero_mass_radical_finrank _).trans (fields_finrank chi _ _)

theorem two_occupied_assignments (q : ChargeLabel H) :
    Occupied (family q).profiles (uniformCharges 0) ∧
      Occupied (family q).profiles (uniformCharges q) := by
  classical
  constructor <;> simp [Occupied, family, uniformCharges, Finsupp.single_apply]

theorem not_pure (q : ChargeLabel H) (hq : q ≠ 0) :
    ¬ ∃ k, (family q).profiles = pure 2 k := by
  rintro ⟨k, hk⟩
  obtain ⟨hzero, hqocc⟩ := two_occupied_assignments q
  rw [hk] at hzero hqocc
  have hz := (occupied_pure_iff 2 (by decide) k _).mp hzero
  have ho := (occupied_pure_iff 2 (by decide) k _).mp hqocc
  exact hq (congrArg StandardBranchProtonObstruction.Charges.quark (ho.trans hz.symm))

/-- A concrete nontrivial order-two character; no group finiteness
hypothesis is needed by the generic construction above. -/
def signCharacter : ℤˣ →* Circle where
  toFun u := if u = 1 then 1 else -1
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl <;> simp

theorem sign_inverse (u : ℤˣ) : signCharacter u⁻¹ = signCharacter u := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

theorem sign_nontrivial : Additive.ofMul signCharacter ≠ 0 := by
  intro he
  have hv := congrArg (fun q : ChargeLabel ℤˣ => (q.toMul (-1) : ℂ)) he
  norm_num [signCharacter] at hv

def nonuniform : ContinuousProfileModel.Model ℤˣ := model signCharacter sign_inverse

theorem nonuniform_not_pure : ¬ ∃ k, nonuniform.profile.profiles = pure 2 k :=
  not_pure _ sign_nontrivial

theorem nonuniform_actual_modes (i : Fin 15) :
    (∃ v : nonuniform.mass.radical.toSubmodule, v ≠ 0 ∧ ∀ g,
      nonuniform.mass.radical.toRepresentation g v =
        keyMonoidHom (smResolvedKey (uniformCharges 0) i) g • v) ∧
    (∃ v : nonuniform.mass.radical.toSubmodule, v ≠ 0 ∧ ∀ g,
      nonuniform.mass.radical.toRepresentation g v =
        keyMonoidHom (smResolvedKey (uniformCharges (Additive.ofMul signCharacter)) i) g • v) := by
  obtain ⟨hzero, hsign⟩ := two_occupied_assignments (Additive.ofMul signCharacter)
  exact ⟨ProfileZeroModeSupport.all_occupied_zeroModes nonuniform.fields nonuniform.mass
    nonuniform.profile.profiles nonuniform.singlets nonuniform.lightTarget _ hzero i,
    ProfileZeroModeSupport.all_occupied_zeroModes nonuniform.fields nonuniform.mass
    nonuniform.profile.profiles nonuniform.singlets nonuniform.lightTarget _ hsign i⟩

theorem nonuniform_result :
    nonuniform.profile.generations = 2 ∧
      Module.finrank ℂ nonuniform.mass.radical.toSubmodule = 54 ∧
      ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
        nonuniform.lightSpectrum :=
  ⟨rfl, model_radical_finrank signCharacter sign_inverse, nonuniform.selection_rule_obstruction⟩

end

end GUT.NonuniformProfileModel
