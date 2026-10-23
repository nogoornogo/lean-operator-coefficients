import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourTensors
import Math.Algebra.Constructions.FourDerivativeWords
import Math.RepresentationTheory.Color.Diagrams.ColoredWavePairing

/-! Four independent field-vector slots on the actual Higgs source. -/
namespace Physics.HiggsQuarticFourFields
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs
abbrev Fields := JetLinear.Field Label
abbrev T := HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs

def fieldWord (r : Fin 5) (i j k l : Fin 4) (v : Fin 4 → Fields) : A :=
  FourDerivativeWords.word D r i j k l (fun t => HiggsInternalSymmetry.fields (v t))
def fieldTensor (f : A →ₗ[ℂ] ℂ) (r : Fin 5) (i j k l : Fin 4) :
    MultilinearMap ℂ (fun _ : Fin 4 => Fields) ℂ :=
  (f.compMultilinearMap (FourDerivativeWords.multilinear D r i j k l)).compLinearMap
    (fun _ => HiggsInternalSymmetry.fields)

theorem fieldTensor_apply (f : A →ₗ[ℂ] ℂ) (r : Fin 5) (i j k l : Fin 4) (v : Fin 4 → Fields) :
    fieldTensor f r i j k l v = f (fieldWord r i j k l v) := rfl

theorem word_basis (r : Fin 5) (i j k l : Fin 4) (a : Fin 4 → Label) :
    fieldWord r i j k l (fun t => Finsupp.single (a t) 1) =
      ColoredQuarticWords.word a r (ColoredQuarticWords.E i) (ColoredQuarticWords.E j)
        (ColoredQuarticWords.E k) (ColoredQuarticWords.E l) := by
  simp only [fieldWord,FourDerivativeWords.word,HiggsInternalSymmetry.fields_single,
    ColoredQuarticWords.word,ColoredQuarticWords.j4,ColoredQuarticWords.j3,
    ColoredQuarticWords.j2,ColoredQuarticWords.j1,ColoredQuarticWords.E,
    ColoredQuarticWords.dirD_single,one_smul,HiggsQuarticFourTensors.field_eq]
  rfl

theorem fieldTensor_basis (f : A →ₗ[ℂ] ℂ) (r : Fin 5) (i j k l : Fin 4) (a : Fin 4 → Label) :
    fieldTensor f r i j k l (fun t => Finsupp.single (a t) 1) =
      f (ColoredQuarticWords.word a r (ColoredQuarticWords.E i) (ColoredQuarticWords.E j)
        (ColoredQuarticWords.E k) (ColoredQuarticWords.E l)) :=
  congrArg f (word_basis r i j k l a)

theorem internal_covariant (g : StandardSMGaugeTensor.GaugeGroup) (r : Fin 5)
    (i j k l : Fin 4) (v : Fin 4 → Fields) : T g (fieldWord r i j k l v) =
      fieldWord r i j k l (fun t => HiggsFieldDictionary.action g (v t)) := by
  simpa only [fieldWord,HiggsInternalSymmetry.fields_covariant,HiggsFieldDictionary.action] using
    FourDerivativeWords.transport_word D (T g)
      (HiggsInternalSymmetry.derivative_commute HiggsFieldDictionary.higgs g)
      r i j k l (fun t => HiggsInternalSymmetry.fields (v t))

theorem internal_basis (f : A →ₗ[ℂ] ℂ) (g : StandardSMGaugeTensor.GaugeGroup)
    (r : Fin 5) (i j k l : Fin 4) (a : Fin 4 → Label) :
    f (T g (ColoredQuarticWords.word a r (ColoredQuarticWords.E i) (ColoredQuarticWords.E j)
      (ColoredQuarticWords.E k) (ColoredQuarticWords.E l))) =
      fieldTensor f r i j k l (fun t => HiggsFieldDictionary.action g (Finsupp.single (a t) 1)) :=
  (congrArg (fun p => f (T g p)) (word_basis r i j k l a)).symm.trans
    (congrArg f (internal_covariant g r i j k l (fun t => Finsupp.single (a t) 1)))

theorem multilinear_ext {f g : MultilinearMap ℂ (fun _ : Fin 4 => Fields) ℂ}
    (he : ∀ a : Fin 4 → Label, f (fun t => Finsupp.single (a t) 1) =
      g (fun t => Finsupp.single (a t) 1)) : f = g := by
  apply Module.Basis.ext_multilinear (fun _ : Fin 4 =>
    (Finsupp.basisSingleOne : Module.Basis Label ℂ Fields))
  intro a
  simpa only [Finsupp.coe_basisSingleOne] using he a

end
end Physics.HiggsQuarticFourFields
