import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsSelection
import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsCommutingControl
import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsProbeControl
import Physics.FieldTheory.Spinor.Weyl.MinkowskiWeylCurrent

/-! Persistent consumers of Li (4.24), Murphy Table 5 and DHM G.1.82.
Density dictionaries and actual input invariance do not imply basis completeness. -/
namespace Physics.WeylHiggsLiterature
set_option autoImplicit false
noncomputable section
open Math PairedWeylKinetic WeylHiggsInput

@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def li : A := DerivativeLiteratureMixed.candidate
def murphy : A := Complex.I • ∑ i : Fin 4,
  MinkowskiWeylCurrent.rightBlock i (0 : Fin 2 → A)
    (DerivativeLiteratureMixed.psi true) (DerivativeLiteratureMixed.psi false) 0 *
    DerivativeLiteratureMixed.higgsCurrent i * DerivativeLiteratureMixed.rho

theorem li_murphy : murphy = li := by
  simp only [murphy, MinkowskiWeylCurrent.right_block_dictionary,
    MinkowskiWeylCurrent.literal_current, li, DerivativeLiteratureMixed.candidate]

theorem li_actual_invariant (g : Group) : action g li = li :=
  WeylHiggsCurrent.candidate_invariant g
theorem murphy_actual_invariant (g : Group) : action g murphy = murphy := by
  rw [li_murphy]
  exact li_actual_invariant g

theorem dhm_block (i : Fin 4) :
    MinkowskiWeylCurrent.rightBlock i (0 : Fin 2 → A)
      (DerivativeLiteratureMixed.psi true) (DerivativeLiteratureMixed.psi false) 0 =
        DerivativeLiteratureMixed.current i := by
  rw [MinkowskiWeylCurrent.right_block_dictionary, MinkowskiWeylCurrent.literal_current]
theorem dhm_reversal (i : Fin 4) : DerivativeLiteratureMixed.current i =
    -MinkowskiWeylCurrent.reversedBar i
      (DerivativeLiteratureMixed.psi false) (DerivativeLiteratureMixed.psi true) :=
  MinkowskiWeylCurrent.literal_reversal i

theorem generated_native_values (f : WeylHiggsRelations.generated.Coefficient) :
    (WeylHiggsRelations.coefficientEquiv f).val murphy = f.val li := by
  rw [li_murphy]
  rfl

def murphySelected : V := ⟨murphy, by
  rw [li_murphy]
  exact WeylHiggsSelection.candidate_grade⟩
theorem selected_native_values (f : WeylHiggsSelection.generatedSelected.Coefficient) :
    (WeylHiggsSelection.selectedCoefficientEquiv f).val murphySelected =
      f.val WeylHiggsSelection.candidate := by
  have he : murphySelected = WeylHiggsSelection.candidate := Subtype.ext li_murphy
  rw [he]
  rfl

theorem raw_value_control : WeylHiggsProbeControl.probe li = Complex.I ∧
    ¬∀ p ∈ input.relations, WeylHiggsProbeControl.probe p = 0 :=
  ⟨WeylHiggsProbeControl.candidate_value, WeylHiggsProbeControl.probe_not_admitted⟩

end
end Physics.WeylHiggsLiterature
