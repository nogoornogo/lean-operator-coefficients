import Math.Audit.ImportOrigin
import Math.LieGroups.Spin.HalfSpin

/-! Actual compact half-spin action, dimensions, and central-character controls.
No SU(5) branching or positive light-target certificate is an input. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod || (`GUT.Sp).isPrefixOf mod then
      throwError "Compact half-spin construction imports another gauge family: {mod}"

namespace Math.CompactSpin.AuditHalfSpin

noncomputable section

open HalfSpin

example : Module.finrank ℂ (Space 1) = 1 := by simpa using finrank 1 (by decide)
example : Module.finrank ℂ (Space 5) = 16 := finrank_sixteen
example : Module.finrank ℂ (HilbertSpace 5) = 16 := hilbert_finrank_sixteen
example : TauCeti.ContRepresentation.IsUnitary (unitaryModel 5) := unitaryModel_unitary 5
example : Continuous (fun p : Group 10 × HilbertSpace 5 => unitaryModel 5 p.1 p.2) :=
  unitaryModel_continuous 5
example : Continuous (fun p : Group 0 × HilbertSpace 0 => unitaryModel 0 p.1 p.2) :=
  unitaryModel_continuous 0

/-- The imaginary coordinate still has positive real norm-square. -/
theorem imaginary_axis_positive :
    Polarized.complexForm 1 (Polarized.coordinates 1 ![0, 1]) = 1 := by
  rw [Polarized.coordinates_form]
  norm_num [Polarized.realForm, TauCeti.realCliffordForm_apply, Fin.sum_univ_succ,
    TauCeti.realCliffordWeight]

theorem central_character_nontrivial :
    (unitaryModel 5).toRepresentation.character centralNegOne ≠
      (unitaryModel 5).toRepresentation.character 1 := by
  rw [unitary_character_centralNegOne, Representation.char_one, hilbert_finrank_sixteen]
  norm_num

example : projection 10 centralNegOne = 1 := projection_centralNegOne
example : ¬ ∃ rho : Representation ℂ (Orthogonal 10) (Space 5),
    representation 5 = rho.comp (projection 10) := not_descends_to_SO

#print axioms Polarized.coordinates_injective
#print axioms Polarized.coordinates_form
#print axioms Polarized.cliffordMap
#print axioms Polarized.cliffordMap_mem_even
#print axioms Polarized.evenMap
#print axioms algebraAction
#print axioms representation
#print axioms finrank
#print axioms finrank_sixteen
#print axioms coefficient_continuous
#print axioms unitaryModel
#print axioms unitaryModel_unitary
#print axioms unitaryModel_continuous
#print axioms unitaryModelEquiv
#print axioms unitaryModel_character
#print axioms hilbert_finrank_sixteen
#print axioms projection_centralNegOne
#print axioms representation_centralNegOne
#print axioms not_descends_to_SO
#print axioms character_centralNegOne
#print axioms unitary_character_centralNegOne
#print axioms imaginary_axis_positive
#print axioms central_character_nontrivial

end

end Math.CompactSpin.AuditHalfSpin
