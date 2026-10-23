import Physics.StandardModel.Operators.Support.Quark.SMQJointPresentation
import Physics.StandardModel.Operators.Support.Quark.SMColoredJointPresentation
import Physics.StandardModel.Operators.Support.Lepton.SMLeptonJointPresentation

/-! Actual presentations of all ten signed single-generation cores.
The finite species dispatch chooses proved decompositions, not computed
multiplicities. All exterior degrees, including overflow, are covered. -/
namespace Physics.SMSignedCoreJointPresentation
set_option autoImplicit false
noncomputable section
open Math Representation JointSourcePresentation

def presentation (s : DeltaLOneSignedInput.Species) (n : ℕ) :
    Presentation ((SMColoredCoreBranching.core s).exteriorPower n) := by
  refine Fin.cases ?_ (fun i1 => ?_) s
  · exact SMQJointPresentation.positive n
  · refine Fin.cases ?_ (fun i2 => ?_) i1
    · exact SMColoredJointPresentation.positive 1 (Or.inl rfl) n
    · refine Fin.cases ?_ (fun i3 => ?_) i2
      · exact SMColoredJointPresentation.positive 2 (Or.inr rfl) n
      · refine Fin.cases ?_ (fun i4 => ?_) i3
        · exact SMLeptonJointPresentation.lepton n
        · refine Fin.cases ?_ (fun i5 => ?_) i4
          · exact SMLeptonJointPresentation.electron n
          · refine Fin.cases ?_ (fun i6 => ?_) i5
            · exact SMQJointPresentation.negative n
            · refine Fin.cases ?_ (fun i7 => ?_) i6
              · exact SMColoredJointPresentation.negative 6 (Or.inl rfl) n
              · refine Fin.cases ?_ (fun i8 => ?_) i7
                · exact SMColoredJointPresentation.negative 7 (Or.inr rfl) n
                · refine Fin.cases ?_ (fun i9 => ?_) i8
                  · exact SMLeptonJointPresentation.conjugateLepton n
                  · refine Fin.cases ?_ (fun i10 => ?_) i9
                    · exact SMLeptonJointPresentation.conjugateElectron n
                    · exact Fin.elim0 i10

theorem allowed_iff (s : DeltaLOneSignedInput.Species) (n : ℕ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((SMColoredCoreBranching.core s).exteriorPower n)) ↔
      JointSourceExpression.Supports (presentation s n).expression :=
  JointSourcePresentation.allowed_iff (presentation s n)

theorem forbidden_iff (s : DeltaLOneSignedInput.Species) (n : ℕ) :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants
      ((SMColoredCoreBranching.core s).exteriorPower n)) ↔
      ¬ JointSourceExpression.Supports (presentation s n).expression :=
  JointSourcePresentation.forbidden_iff (presentation s n)

end
end Physics.SMSignedCoreJointPresentation
