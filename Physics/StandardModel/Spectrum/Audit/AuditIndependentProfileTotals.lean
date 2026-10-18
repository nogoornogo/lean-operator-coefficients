import Physics.StandardModel.Spectrum.FiniteChargeProfiles
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Unequal positive totals are permitted by the coefficient endpoint.
This is not an anomaly-consistent matter-model construction. -/

set_option autoImplicit false

namespace GUT.FiniteChargeProfiles.AuditIndependentTotals

noncomputable section
open FiniteAbelianChargeSectors

abbrev Residual := Multiplicative (ZMod 3)

def unequal : Profiles (ChargeLabel Residual) :=
  ⟨Finsupp.single 0 2, Finsupp.single 0 2, Finsupp.single 0 1,
    Finsupp.single 0 1, Finsupp.single 0 2⟩

theorem unequal_no_common_total : ¬ ∃ n, HasCommonTotal unequal n := by
  rintro ⟨n, hn⟩
  have hQ := hn.quark
  have hD := hn.down
  simp [unequal] at hQ hD
  omega

theorem unequal_supported_neutral : ∃ k, Occupied unequal k ∧
    protonFirstCharacter k = 1 ∧ protonSecondCharacter k = 1 := by
  apply exists_occupied_trivial_characters_of_positive_totals unequal
  · simp [unequal]
  · simp [unequal]
  · exact ⟨rfl, rfl, rfl⟩

end
end GUT.FiniteChargeProfiles.AuditIndependentTotals

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Independent totals imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.FiniteChargeProfiles.exists_occupied_compatible_of_positive_totals,
    ``GUT.FiniteChargeProfiles.exists_occupied_trivial_characters_of_positive_totals,
    ``GUT.FiniteChargeProfiles.AuditIndependentTotals.unequal_no_common_total,
    ``GUT.FiniteChargeProfiles.AuditIndependentTotals.unequal_supported_neutral]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Independent totals: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Independent totals: import boundary and {declarations.length} strict transitive axiom checks passed"
