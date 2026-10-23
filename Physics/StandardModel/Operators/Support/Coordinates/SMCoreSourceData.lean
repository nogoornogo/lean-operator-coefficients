import Math.RepresentationTheory.Color.Diagrams.ColoredSourceData
import Math.RepresentationTheory.Constructions.JointSourceReexpression
import Physics.StandardModel.Operators.Support.Joint.SMSignedCoreJointPresentation

/-! Executable SM core metadata is the outer field of an actual presentation.
Reuse the mathematical expression proofs before transporting representations;
no comparison with the old dependent dispatch projection is required. -/
namespace Physics.SMCoreSourceData
set_option autoImplicit false
open Math JointSourceExpression JointSourcePresentation
open scoped TensorProduct

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup (SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    (Module.Dual ℂ (SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((Module.Dual ℂ SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance

def coreData (s : DeltaLOneSignedInput.Species) (n : Nat) : Expr :=
  match s.val with
  | 0 => JointSourceData.quark false n
  | 1 => JointSourceData.colored true n
  | 2 => JointSourceData.colored true n
  | 3 => JointSourceData.doubletPair false n
  | 4 => JointSourceData.single true n
  | 5 => JointSourceData.dual (JointSourceData.quark true n)
  | 6 => JointSourceData.dual (JointSourceData.colored false n)
  | 7 => JointSourceData.dual (JointSourceData.colored false n)
  | 8 => JointSourceData.doubletPair true n
  | _ => JointSourceData.single false n


noncomputable def qPresentation (n : Nat) :
    Presentation ((SMColoredCoreBranching.core 0).exteriorPower n) :=
  alongEquiv (SMQCoreBranching.positiveEquiv.exteriorPower n)
    (reexpress (SU3DoubleSpinAllPresentation.positive false n) (JointSourceData.quark false n)
      (JointSourceData.quark_eq false n))

noncomputable def coloredPresentation (s : DeltaLOneSignedInput.Species) (hs : s=1 ∨ s=2) (n : Nat) :
    Presentation ((SMColoredCoreBranching.core s).exteriorPower n) :=
  alongEquiv (SMColoredCoreBranching.positiveExteriorEquiv s hs n)
    (reexpress (SU3SpinJointPresentation.positive true n) (JointSourceData.colored true n)
      (JointSourceData.colored_eq true n))

noncomputable def leptonPresentation (n : Nat) :
    Presentation ((SMColoredCoreBranching.core 3).exteriorPower n) :=
  alongEquiv (SMLeptonCoreBranching.exteriorEquiv n)
    (reexpress (SU2PairJointPresentation.positive false n) (JointSourceData.doubletPair false n)
      (JointSourceData.doubletPair_eq false n))

noncomputable def electronPresentation (n : Nat) :
    Presentation ((SMColoredCoreBranching.core 4).exteriorPower n) :=
  alongEquiv (SMLeptonJointPresentation.electronModel.exteriorPower n)
    (reexpress (SU2SingleJointPresentation.positive true n) (JointSourceData.single true n)
      (JointSourceData.single_eq true n))

noncomputable def conjugateQPresentation (n : Nat) :
    Presentation ((SMColoredCoreBranching.core 5).exteriorPower n) :=
  alongEquiv (SMQCoreBranching.negativeEquiv.exteriorPower n)
    (reexpress (SU3DoubleSpinAllPresentation.negative true n)
      (JointSourceData.dual (JointSourceData.quark true n)) (JointSourceData.conjugateQuark_eq true n))

noncomputable def conjugateColoredPresentation (s : DeltaLOneSignedInput.Species) (hs : s=6 ∨ s=7) (n : Nat) :
    Presentation ((SMColoredCoreBranching.core s).exteriorPower n) :=
  alongEquiv (SMColoredCoreBranching.negativeExteriorEquiv s hs n)
    (reexpress (SU3SpinJointPresentation.negative false n)
      (JointSourceData.dual (JointSourceData.colored false n)) (JointSourceData.conjugateColored_eq false n))

noncomputable def conjugateLeptonPresentation (n : Nat) :
    Presentation ((SMColoredCoreBranching.core 8).exteriorPower n) :=
  alongEquiv (SMLeptonJointPresentation.conjugateLeptonEquiv.exteriorPower n)
    (reexpress (SU2PairJointPresentation.positive true n) (JointSourceData.doubletPair true n)
      (JointSourceData.doubletPair_eq true n))

noncomputable def conjugateElectronPresentation (n : Nat) :
    Presentation ((SMColoredCoreBranching.core 9).exteriorPower n) :=
  alongEquiv (SMLeptonJointPresentation.conjugateElectronModel.exteriorPower n)
    (reexpress (SU2SingleJointPresentation.positive false n) (JointSourceData.single false n)
      (JointSourceData.single_eq false n))

/-- The expression is explicit before the dependent equivalence dispatch. -/
noncomputable def corePresentation (s : DeltaLOneSignedInput.Species) (n : Nat) :
    Presentation ((SMColoredCoreBranching.core s).exteriorPower n) where
  expression := coreData s n
  equivalence := by
    refine Fin.cases ?_ (fun i1 => ?_) s
    · exact (qPresentation n).equivalence
    · refine Fin.cases ?_ (fun i2 => ?_) i1
      · exact (coloredPresentation 1 (Or.inl rfl) n).equivalence
      · refine Fin.cases ?_ (fun i3 => ?_) i2
        · exact (coloredPresentation 2 (Or.inr rfl) n).equivalence
        · refine Fin.cases ?_ (fun i4 => ?_) i3
          · exact (leptonPresentation n).equivalence
          · refine Fin.cases ?_ (fun i5 => ?_) i4
            · exact (electronPresentation n).equivalence
            · refine Fin.cases ?_ (fun i6 => ?_) i5
              · exact (conjugateQPresentation n).equivalence
              · refine Fin.cases ?_ (fun i7 => ?_) i6
                · exact (conjugateColoredPresentation 6 (Or.inl rfl) n).equivalence
                · refine Fin.cases ?_ (fun i8 => ?_) i7
                  · exact (conjugateColoredPresentation 7 (Or.inr rfl) n).equivalence
                  · refine Fin.cases ?_ (fun i9 => ?_) i8
                    · exact (conjugateLeptonPresentation n).equivalence
                    · refine Fin.cases ?_ (fun i10 => Fin.elim0 i10) i9
                      exact (conjugateElectronPresentation n).equivalence

theorem corePresentation_expression (s : DeltaLOneSignedInput.Species) (n : Nat) :
    (corePresentation s n).expression = coreData s n := rfl

end Physics.SMCoreSourceData
