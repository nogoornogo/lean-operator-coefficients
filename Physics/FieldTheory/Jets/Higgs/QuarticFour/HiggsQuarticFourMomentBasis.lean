import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourFields
import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourWaves
import Math.Algebra.HiggsFourWaveCubature.Basic

/-! Relation-annihilating ordered wave sums and their invariant internal model. -/
namespace Physics.HiggsQuarticFourMomentBasis
set_option autoImplicit false
noncomputable section
open Math MvPolynomial DerivativeLiteratureHiggs
open ColoredQuarticWords (word E)
open ColoredFourWavePolarization (assignments orders)
abbrev count := HiggsFourWaveCubature.count
def momenta (r : Fin 3) (a : Fin (count r)) (s i : Fin 4) : ℂ :=
  GaussianInt.toComplex (HiggsFourWaveCubature.raw r a s i)
def scale (r : Fin 3) : ℂ := 1/(16*(count r : ℂ))

theorem conservation (r : Fin 3) (a : Fin (count r)) (i : Fin 4) :
    ∑ s : Fin 4, momenta r a s i = 0 := by
  have he := congrArg GaussianInt.toComplex (HiggsFourWaveCubature.conservation r a i)
  simpa only [map_sum,map_zero,momenta] using he
theorem null (r : Fin 3) (a : Fin (count r)) (s : Fin 4) :
    (momenta r a s 0)^2-(momenta r a s 1)^2-(momenta r a s 2)^2-(momenta r a s 3)^2 = 0 := by
  have he := congrArg GaussianInt.toComplex (HiggsFourWaveCubature.null r a s)
  simpa only [map_sub,map_pow,map_zero,momenta] using he

def functional (r : Fin 3) : A →ₗ[ℂ] ℂ := scale r •
  ∑ x : Fin 2, ∑ y : Fin 2, ∑ a : Fin (count r),
    ColoredFourWaveEvaluation.onJets (momenta r a) (ColoredWavePairing.amplitudes x y)

theorem annihilates (r : Fin 3) : HiggsQuarticFourInput.P.relations ≤ (functional r).ker := by
  intro p hp
  have hz (x y : Fin 2) (a : Fin (count r)) :
      ColoredFourWaveEvaluation.onJets (momenta r a) (ColoredWavePairing.amplitudes x y) p = 0 :=
    HiggsQuarticFourWaves.annihilates _ _ (conservation r a) (null r a) hp
  change functional r p = 0
  simp only [functional,LinearMap.smul_apply,LinearMap.sum_apply,hz,
    Finset.sum_const_zero,smul_zero]

theorem sum_moment (r : Fin 3) (s t u v i j k l : Fin 4) :
    (∑ a : Fin (count r), momenta r a s i*momenta r a t j*momenta r a u k*momenta r a v l) =
      GaussianInt.toComplex (HiggsFourWaveCubature.sumMoment r s t u v i j k l) := by
  simp only [momenta,HiggsFourWaveCubature.sumMoment,map_sum,map_mul]

theorem word_value (r : Fin 3) (a : Fin 4 → Label) (t : Fin 5) (i j k l : Fin 4) :
    functional r (word a t (E i) (E j) (E k) (E l)) = scale r*∑ p : Fin 24,
      ColoredWavePairing.tensor p (fun n => Finsupp.single (a n) 1)*
        GaussianInt.toComplex (HiggsFourWaveCubature.sumMoment r
          (assignments p (orders t 0)) (assignments p (orders t 1))
          (assignments p (orders t 2)) (assignments p (orders t 3)) i j k l) := by
  simp only [functional,LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul,
    ColoredFourWavePolarization.word_value,ColoredFourWavePolarization.moment_expansion]
  rw [ColoredFourWavePolarization.sum_reorder]
  simp only [ColoredWavePairing.amplitude_sum_pairing,sum_moment]

def fieldModel (r : Fin 3) (t : Fin 5) (i j k l : Fin 4) :
    MultilinearMap ℂ (fun _ : Fin 4 => HiggsQuarticFourFields.Fields) ℂ :=
  ∑ p : Fin 24, (scale r*GaussianInt.toComplex (HiggsFourWaveCubature.sumMoment r
    (assignments p (orders t 0)) (assignments p (orders t 1))
    (assignments p (orders t 2)) (assignments p (orders t 3)) i j k l)) •
      ColoredWavePairing.tensor p

theorem fieldTensor_eq (r : Fin 3) (t : Fin 5) (i j k l : Fin 4) :
    HiggsQuarticFourFields.fieldTensor (functional r) t i j k l = fieldModel r t i j k l := by
  apply HiggsQuarticFourFields.multilinear_ext
  intro a
  rw [HiggsQuarticFourFields.fieldTensor_basis,word_value]
  simp only [fieldModel,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem fieldModel_invariant (r : Fin 3) (t : Fin 5) (i j k l : Fin 4)
    (g : StandardSMGaugeTensor.GaugeGroup) (v : Fin 4 → HiggsQuarticFourFields.Fields) :
    fieldModel r t i j k l (fun n => HiggsFieldDictionary.action g (v n)) =
      fieldModel r t i j k l v := by
  simp only [fieldModel,_root_.sum_apply,_root_.smul_apply,
    HiggsFieldDictionary.action,ColoredWavePairing.tensor_invariant]

theorem internal_word (r : Fin 3) (g : StandardSMGaugeTensor.GaugeGroup)
    (a : Fin 4 → Label) (t : Fin 5) (i j k l : Fin 4) :
    functional r (HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs g
      (word a t (E i) (E j) (E k) (E l))) = functional r (word a t (E i) (E j) (E k) (E l)) := by
  rw [HiggsQuarticFourFields.internal_basis,fieldTensor_eq,fieldModel_invariant,
    ← fieldTensor_eq,HiggsQuarticFourFields.fieldTensor_basis]

theorem internal (r : Fin 3) (g : StandardSMGaugeTensor.GaugeGroup) (p : HiggsQuarticFourInput.V) :
    functional r (HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs g p.val) =
      functional r p.val := by
  have hp : p.val ∈ ColoredQuarticSource.wordSpan Label := by
    rw [← ColoredQuarticSource.grade_eq_span]
    exact p.property
  refine Submodule.span_induction (p := fun p _ =>
    functional r (HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs g p) = functional r p)
    ?_ ?_ ?_ ?_ hp
  · rintro p ⟨a,t,i,j,k,l,rfl⟩
    exact internal_word r g a t i j k l
  · simp
  · intro p q _ _ hp hq; simp only [map_add,hp,hq]
  · intro c p _ hp; simp only [map_smul,hp]

end
end Physics.HiggsQuarticFourMomentBasis
