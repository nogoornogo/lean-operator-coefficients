import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourMomentInvariance

/-! Exact normalizations of the three actual ordered-wave coefficient candidates. -/
namespace Physics.HiggsQuarticFourMomentValues
set_option autoImplicit false
noncomputable section
open Math MvPolynomial DerivativeLiteratureHiggs
open HiggsQuarticFourMomentBasis HiggsQuarticFourMomentInvariance
open ColoredQuarticWords (word E)
open ColoredFourWavePolarization (assignments orders)

def pairProduct (a : Fin 4 → Label) : A :=
  pair (h (a 0).1 (a 0).2) (h (a 1).1 (a 1).2)*pair (h (a 2).1 (a 2).2) (h (a 3).1 (a 3).2)
theorem metric_eta (i : Fin 4) : metric i = LorentzRankFour.eta i := by fin_cases i <;> rfl

theorem pair_word (a : Fin 4 → Label) : pairProduct a =
    ∑ i : Fin 4, ∑ j : Fin 4, (LorentzRankFour.eta i*LorentzRankFour.eta j) •
      word a 4 (E i) (E i) (E j) (E j) := by
  rw [pairProduct,HiggsQuarticFourInput.pair_dot,HiggsQuarticFourInput.pair_dot]
  simp only [HiggsQuarticFourInput.dot,Finset.sum_mul,Finset.mul_sum,
    smul_mul_assoc,mul_smul_comm,Finset.smul_sum,smul_smul,metric_eta]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (LorentzRankFour.eta j) (LorentzRankFour.eta i)]
  apply congrArg (fun p : A => (LorentzRankFour.eta i*LorentzRankFour.eta j) • p)
  simp only [word,ColoredQuarticWords.j1,ColoredQuarticWords.dirD_single,one_smul,
    HiggsQuarticFourTensors.field_eq]
  ring

theorem pair_value_trace (r : Fin 3) (hM : Moments r) (a : Fin 4 → Label) :
    functional r (pairProduct a) =
      16*coordinate r a 4 0+4*coordinate r a 4 1+4*coordinate r a 4 2 := by
  rw [pair_word,map_sum]
  simp only [map_sum,map_smul,smul_eq_mul]
  exact LorentzRankFourThree.double_trace (ColoredQuarticWords.tensor (functional r) a 4)
    (coordinate r a 4 0) (coordinate r a 4 1) (coordinate r a 4 2)
    (fun i j k l => basis_formula r hM a 4 i j k l)

theorem scale_factor (r : Fin 3) :
    scale r*72*GaussianInt.toComplex (HiggsFourWaveCubature.factor r) = (1/16 : ℂ) := by
  fin_cases r <;> norm_num [scale,count,HiggsFourWaveCubature.count,HiggsFourWaveCubature.factor,
    GaussianInt.toComplex]

theorem trace_channels (r : Fin 3) (a : Fin 4 → Label) :
    16*coordinate r a 4 0+4*coordinate r a 4 1+4*coordinate r a 4 2 =
      (1/16 : ℂ)*GaussianInt.toComplex (HiggsFourWaveCubature.KSum r a) := by
  let w (p : Fin 24) := ColoredWavePairing.tensor p (fun n => Finsupp.single (a n) 1)
  have hp (p : Fin 24) : 16*(w p*channel r 4 p 0)+4*(w p*channel r 4 p 1)+4*(w p*channel r 4 p 2) =
      72*GaussianInt.toComplex (HiggsFourWaveCubature.factor r)*
        ((ColoredWavePairing.internalInt a p : ℂ)*
          GaussianInt.toComplex (HiggsFourWaveCubature.gram r (assignments p 0) (assignments p 1))*
          GaussianInt.toComplex (HiggsFourWaveCubature.gram r (assignments p 2) (assignments p 3))) := by
    have he := congrArg GaussianInt.toComplex (HiggsFourWaveCubature.channel_trace r
      (assignments p 0) (assignments p 1) (assignments p 2) (assignments p 3))
    simp only [map_add,map_mul,map_ofNat] at he
    have hc : 16*channel r 4 p 0+4*channel r 4 p 1+4*channel r 4 p 2 =
        72*GaussianInt.toComplex (HiggsFourWaveCubature.factor r)*
          GaussianInt.toComplex (HiggsFourWaveCubature.gram r (assignments p 0) (assignments p 1))*
          GaussianInt.toComplex (HiggsFourWaveCubature.gram r (assignments p 2) (assignments p 3)) := by
      simpa [channel,orders] using he
    have hw : w p = (ColoredWavePairing.internalInt a p : ℂ) := ColoredWavePairing.tensor_basis_int a p
    rw [hw]
    linear_combination (ColoredWavePairing.internalInt a p : ℂ)*hc
  calc
    _ = scale r*(16*(∑ p : Fin 24, w p*channel r 4 p 0)+
        4*(∑ p : Fin 24, w p*channel r 4 p 1)+4*(∑ p : Fin 24, w p*channel r 4 p 2)) := by
      dsimp only [coordinate,w]
      ring
    _ = scale r*∑ p : Fin 24,
        (16*(w p*channel r 4 p 0)+4*(w p*channel r 4 p 1)+4*(w p*channel r 4 p 2)) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib]
    _ = scale r*∑ p : Fin 24, 72*GaussianInt.toComplex (HiggsFourWaveCubature.factor r)*
        ((ColoredWavePairing.internalInt a p : ℂ)*
          GaussianInt.toComplex (HiggsFourWaveCubature.gram r (assignments p 0) (assignments p 1))*
          GaussianInt.toComplex (HiggsFourWaveCubature.gram r (assignments p 2) (assignments p 3))) := by
      simp only [hp]
    _ = (scale r*72*GaussianInt.toComplex (HiggsFourWaveCubature.factor r))*
        GaussianInt.toComplex (HiggsFourWaveCubature.KSum r a) := by
      simp only [HiggsFourWaveCubature.KSum,map_sum,map_mul,map_intCast,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by rw [scale_factor]

theorem pair_value (r : Fin 3) (hM : Moments r) (a : Fin 4 → Label) :
    functional r (pairProduct a) = (1/16 : ℂ)*GaussianInt.toComplex (HiggsFourWaveCubature.KSum r a) :=
  (pair_value_trace r hM a).trans (trace_channels r a)

theorem native_pair_value (r : Fin 3) (hM : Moments r) (i : Fin 7) :
    functional r (pairProduct (HiggsFourWaveCubature.pairLabels i)) =
      (HiggsFourWaveCubature.KValue r i : ℂ) := by
  rw [pair_value r hM,HiggsFourWaveCubature.KSum_values]
  simp only [map_mul,map_ofNat,map_intCast]
  ring

theorem seven_pair (i : Fin 7) : HiggsQuarticFourInternalUpper.seven i =
    pairProduct (HiggsFourWaveCubature.pairLabels i) := by
  fin_cases i <;> rfl

theorem seven_value (r : Fin 3) (hM : Moments r) (i : Fin 7) :
    functional r (HiggsQuarticFourInternalUpper.seven i) = (HiggsFourWaveCubature.KValue r i : ℂ) :=
  (congrArg (functional r) (seven_pair i)).trans (native_pair_value r hM i)

def values : Fin 3 → Fin 3 → ℂ := ![![12,48,12],![32,48,16],![16,48,32]]

theorem q1_value (r : Fin 3) (hM : Moments r) : functional r q1 = values r 0 := by
  have he := congrArg (functional r) HiggsQuarticFourInternalUpper.q1_K
  have h3 : functional r (HiggsQuarticFourInternalUpper.K 0 2 0 2) =
      (HiggsFourWaveCubature.KValue r 3 : ℂ) := seven_value r hM 3
  have h5 : functional r (HiggsQuarticFourInternalUpper.K 1 3 1 3) =
      (HiggsFourWaveCubature.KValue r 5 : ℂ) := seven_value r hM 5
  have h6 : functional r (HiggsQuarticFourInternalUpper.K 0 3 1 2) =
      (HiggsFourWaveCubature.KValue r 6 : ℂ) := seven_value r hM 6
  simp only [map_add,map_smul,smul_eq_mul,h3,h5,h6] at he
  refine he.trans ?_
  fin_cases r <;> norm_num [HiggsFourWaveCubature.KValue,values]
theorem q2_value (r : Fin 3) (hM : Moments r) : functional r q2 = values r 1 := by
  have he := congrArg (functional r) HiggsQuarticFourInternalUpper.q2_K
  have h0 : functional r (HiggsQuarticFourInternalUpper.K 0 0 2 2) =
      (HiggsFourWaveCubature.KValue r 0 : ℂ) := seven_value r hM 0
  have h2 : functional r (HiggsQuarticFourInternalUpper.K 1 1 3 3) =
      (HiggsFourWaveCubature.KValue r 2 : ℂ) := seven_value r hM 2
  have h1 : functional r (HiggsQuarticFourInternalUpper.K 0 1 2 3) =
      (HiggsFourWaveCubature.KValue r 1 : ℂ) := seven_value r hM 1
  simp only [map_add,map_smul,smul_eq_mul,h0,h2,h1] at he
  refine he.trans ?_
  fin_cases r <;> norm_num [HiggsFourWaveCubature.KValue,values]
theorem q3_value (r : Fin 3) (hM : Moments r) : functional r q3 = values r 2 := by
  have he := congrArg (functional r) HiggsQuarticFourInternalUpper.q3_K
  have h3 : functional r (HiggsQuarticFourInternalUpper.K 0 2 0 2) =
      (HiggsFourWaveCubature.KValue r 3 : ℂ) := seven_value r hM 3
  have h5 : functional r (HiggsQuarticFourInternalUpper.K 1 3 1 3) =
      (HiggsFourWaveCubature.KValue r 5 : ℂ) := seven_value r hM 5
  have h4 : functional r (HiggsQuarticFourInternalUpper.K 0 2 1 3) =
      (HiggsFourWaveCubature.KValue r 4 : ℂ) := seven_value r hM 4
  simp only [map_add,map_smul,smul_eq_mul,h3,h5,h4] at he
  refine he.trans ?_
  fin_cases r <;> norm_num [HiggsFourWaveCubature.KValue,values]

theorem representative_value (r : Fin 3) (hM : Moments r) (i : Fin 3) :
    functional r (HiggsQuarticFourInput.representatives i).val = values r i := by
  fin_cases i
  · exact q1_value r hM
  · exact q2_value r hM
  · exact q3_value r hM

end
end Physics.HiggsQuarticFourMomentValues
