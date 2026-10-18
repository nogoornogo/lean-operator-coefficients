import Math.Audit.ImportOrigin
import Physics.StandardModel.Spectrum.SelfDualChirality
import Physics.StandardModel.Spectrum.Audit.AuditProfileChiralIndex
import Physics.FieldTheory.Mass.Audit.AuditAbelianMassSpectrum

open Math

/-! DUAL-2 coefficient controls and the distinction between gauge and
charge-resolved self-duality. Only the legacy SU(5) weight combinatorics,
not an actual SU(5) group or source representation, is imported. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod ||
        ((`GUT.SU5).isPrefixOf mod &&
          mod != `GUT.SU5.Branching.WeylOrbit && mod != `GUT.SU5.Branching.ChargeResolved) then
      throwError "Self-dual SM target core imports a GUT source module: {mod}"

namespace GUT.AuditSelfDualChirality

noncomputable section

open SelfDualChirality StandardAbelianCharge StandardSMCharacterTarget StandardWeylDualTarget
open FiniteChargeProfiles AuditFiniteChargeProfiles AuditAbelianMassSpectrum
open FiniteAbelianChargeSectors

abbrev Label := ChargeLabel (Multiplicative (ZMod 2))

theorem torsion_forgotten_coefficient (s : Label →₀ ℤ) :
    forgetCharges (chiralDifference
      (targetWithSinglets (mixedFamily (cyclicLabels 2 1)).profiles s))
        (smReducedWeight 0) = 3 :=
  forgotten_target_coefficient _ 3 (mixedFamily _).totals s 0

theorem torsion_target_nonzero (s : Label →₀ ℤ) :
    forgetCharges (chiralDifference
      (targetWithSinglets (mixedFamily (cyclicLabels 2 1)).profiles s)) ≠ 0 :=
  forgotten_target_ne_zero (mixedFamily _) s

theorem zero_generation_control (k : StandardBranchProtonObstruction.Charges Label)
    (s : Label →₀ ℤ) :
    forgetCharges (chiralDifference (targetWithSinglets (pure 0 k) s)) = 0 := by
  rw [forgetCharges_chiralDifference, forgetCharges_targetWithSinglets (pure_totals 0 k)]
  simp [gaugeDualDifference, unchargedTarget]

theorem vectorlike_pairs_do_not_remove_obstruction (F : Family Label) (s : Label →₀ ℤ)
    (r : ResolvedCharacter Label) :
    forgetCharges (chiralDifference (targetWithSinglets F.profiles s +
      (r + dualCharacter r))) ≠ 0 := by
  rw [chiralDifference_add_vectorlike]
  exact forgotten_target_ne_zero F s

def chargedGaugeSinglet : Representation ℂ (ℤˣ × Circle) ℂ :=
  scalar (MonoidHom.snd ℤˣ Circle)

theorem gauge_only_self_dual (g : ℤˣ) :
    chargedGaugeSinglet.character (g, 1) = chargedGaugeSinglet.dual.character (g, 1) := by
  rw [Representation.char_dual]
  simp [chargedGaugeSinglet, scalar_character]

/-- Gauge self-duality cannot be promoted to residual-charge self-duality. -/
theorem not_charge_resolved_self_dual :
    chargedGaugeSinglet.character (1, imaginaryUnit) ≠
      chargedGaugeSinglet.dual.character (1, imaginaryUnit) := by
  rw [Representation.char_dual]
  change (scalar (MonoidHom.snd ℤˣ Circle)).character _ ≠
    (scalar (MonoidHom.snd ℤˣ Circle)).character _
  rw [scalar_character, scalar_character]
  change Complex.I ≠ (imaginaryUnit⁻¹ : Circle)
  rw [Circle.coe_inv]
  change Complex.I ≠ Complex.I⁻¹
  norm_num [Complex.ext_iff]

#print axioms forgetCharges_chiralDifference
#print axioms forgotten_target_coefficient
#print axioms forgotten_target_ne_zero
#print axioms evaluateGauge_injective
#print axioms evaluated_target_not_zero
#print axioms not_has_target_of_zero_source
#print axioms not_has_target_of_source_equiv
#print axioms not_has_target_of_inverse_conjugacy
#print axioms torsion_forgotten_coefficient
#print axioms torsion_target_nonzero
#print axioms zero_generation_control
#print axioms vectorlike_pairs_do_not_remove_obstruction
#print axioms gauge_only_self_dual
#print axioms not_charge_resolved_self_dual

end

end GUT.AuditSelfDualChirality
