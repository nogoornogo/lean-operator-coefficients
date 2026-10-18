import Math.Audit.ImportOrigin
import Math.Topology.CompactCharacters

/-! Character triviality needs both compactness and simple connectedness.
These controls do not use a concrete gauge group. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod ||
        (`GUT.SUN).isPrefixOf mod || (`GUT.Spin).isPrefixOf mod || (`GUT.Sp).isPrefixOf mod then
      throwError "Generic compact-character audit imports a gauge family: {mod}"

namespace Math.CompactCharacters.Audit

theorem circle_character_nontrivial :
    Continuous Circle.coeHom ∧ Circle.coeHom (-1) ≠ 1 := by
  exact ⟨continuous_subtype_val, by change (-1 : ℂ) ≠ 1; norm_num⟩

theorem noncompact_real_character :
    Continuous (MonoidHom.id (Multiplicative ℝ)) ∧
      Multiplicative.toAdd (MonoidHom.id (Multiplicative ℝ) (Multiplicative.ofAdd 1)) ≠ 0 := by
  exact ⟨continuous_id, by norm_num⟩

example (z : Circle) : ‖Circle.coeHom z‖ = 1 := by
  let : CompactSpace Circle := inferInstance
  apply complex_norm_eq_one (H := Circle) Circle.coeHom
  exact continuous_subtype_val

#print axioms real_eq_zero
#print axioms complex_norm_eq_one
#print axioms circle_eq_one
#print axioms complex_eq_one
#print axioms circle_character_nontrivial
#print axioms noncompact_real_character

end Math.CompactCharacters.Audit
