import Math.Audit.ImportOrigin
import Physics.FieldTheory.Mass.Surplus.SurjectiveMassDescent
import Math.RepresentationTheory.Characters.UnitarySpectrumRestriction
import Physics.FieldTheory.Mass.Spectrum.Audit.AuditAbelianMassSpectrum

open Math

/-! A nonzero mass survives descent. A nonsurjective restriction merges
different characters, demonstrating why full multiplicity recovery needs
surjectivity. These controls have no gauge-specific dependency. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod then
      throwError "Surjective mass audit imports a gauge-specific module: {mod}"

namespace Physics.AuditSurjectiveMassDescent

noncomputable section

open InvariantWeylMass AuditAbelianMassSpectrum UnitaryCharacterSpectrum AbelianActualSpectrum

def projection : Circle × ℤˣ →* Circle := MonoidHom.fst _ _

theorem projection_surjective : Function.Surjective projection := fun z => ⟨(z, 1), rfl⟩

def coveredMass : SymmetricMass (pairAction.comp projection) where
  form := pairMass.form
  symmetric := pairMass.symmetric
  invariant g := pairMass.invariant g.1

theorem descended_form :
    (SymmetricMass.descend pairAction projection projection_surjective coveredMass).form =
      pairMass.form := rfl

theorem descended_nonzero :
    (SymmetricMass.descend pairAction projection projection_surjective coveredMass).form ≠ 0 :=
  pairMass_nonzero

theorem projected_multiplicity (chi : Circle →* ℂ) :
    spectrum (pairAction.comp projection) (comp_unitary pairAction pair_unitary projection)
      (chi.comp projection) = spectrum pairAction pair_unitary chi :=
  spectrum_comp_apply pairAction pair_unitary projection projection_surjective chi

def collapse : Circle →* Circle := 1

theorem collapse_not_surjective : ¬ Function.Surjective collapse := by
  intro h
  obtain ⟨z, hz⟩ := h imaginaryUnit
  have he := congrArg (fun t : Circle => (t : ℂ).im) hz
  norm_num [collapse, imaginaryUnit] at he

theorem collapse_spectrum :
    spectrum (pairAction.comp collapse) (comp_unitary pairAction pair_unitary collapse) =
      Finsupp.single (1 : Circle →* ℂ) 2 := by
  apply eval_injective
  intro z
  rw [spectrum_eval, eval_single]
  change pairAction.character 1 = (2 : ℂ) * 1
  rw [pair_character]
  norm_num

#print axioms SymmetricMass.descend
#print axioms SymmetricMass.descend_form
#print axioms SymmetricMass.descend_radical_comp
#print axioms SymmetricMass.descend_radical_character
#print axioms spectrum_comp
#print axioms spectrum_comp_apply
#print axioms descended_nonzero
#print axioms projected_multiplicity
#print axioms collapse_not_surjective
#print axioms collapse_spectrum

end

end Physics.AuditSurjectiveMassDescent
