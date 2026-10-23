import Math.Algebra.HiggsFourWaveCubature.Structural.TransverseSymmetry

/-! Gram contractions determine all three coefficients of the transverse moment tensor. -/
namespace Math.HiggsFourWaveCubature.Structural.Transverse
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators

private theorem paired_sums (f g h q : Fin 288 → Fin 4 → GaussianInt) :
    (∑ i : Fin 4, ∑ j : Fin 4, ∑ a : Fin 288, f a i*g a i*h a j*q a j) =
      ∑ a : Fin 288, (∑ i : Fin 4,f a i*g a i)*(∑ j : Fin 4,h a j*q a j) := by
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem trace_ab (s t u v : Fin 4) :
    (∑ i : Fin 4, ∑ j : Fin 4, tensor s t u v ![i,i,j,j]) =
      288*(gram 0 s t*gram 0 u v) := by
  change (∑ i : Fin 4, ∑ j : Fin 4, ∑ a : Fin 288,
    euclid a s i*euclid a t i*euclid a u j*euclid a v j) = _
  rw [paired_sums]
  calc
    _ = ∑ a : Fin 288, gramSign a^2*(gram 0 s t*gram 0 u v) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [gram_covariant,gram_covariant]
      ring
    _ = _ := by simp only [gramSign_square,one_mul,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin]; norm_num

private theorem trace_ac (s t u v : Fin 4) :
    (∑ i : Fin 4, ∑ j : Fin 4, tensor s t u v ![i,j,i,j]) =
      288*(gram 0 s u*gram 0 t v) := by
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, tensor s u t v ![i,i,j,j] := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      unfold tensor
      apply Finset.sum_congr rfl
      intro a _
      dsimp
      ring
    _ = _ := trace_ab s u t v

private theorem trace_ad (s t u v : Fin 4) :
    (∑ i : Fin 4, ∑ j : Fin 4, tensor s t u v ![i,j,j,i]) =
      288*(gram 0 s v*gram 0 t u) := by
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, tensor s v t u ![i,i,j,j] := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      unfold tensor
      apply Finset.sum_congr rfl
      intro a _
      dsimp
      ring
    _ = _ := trace_ab s v t u

private theorem trace_shape (B C D : GaussianInt) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      (B*delta i i*delta j j+C*delta i j*delta i j+D*delta i j*delta i j)) = 16*B+4*C+4*D ∧
    (∑ i : Fin 4, ∑ j : Fin 4,
      (B*delta i j*delta i j+C*delta i i*delta j j+D*delta i j*delta j i)) = 4*B+16*C+4*D ∧
    (∑ i : Fin 4, ∑ j : Fin 4,
      (B*delta i j*delta j i+C*delta i j*delta j i+D*delta i i*delta j j)) = 4*B+4*C+16*D := by
  refine ⟨?_,?_,?_⟩ <;> norm_num [Fin.sum_univ_succ,delta] <;> ring

private theorem coefficients (s t u v : Fin 4) :
    tensor s t u v ![0,0,1,1] =
      4*(5*(gram 0 s t*gram 0 u v)-gram 0 s u*gram 0 t v-gram 0 s v*gram 0 t u) ∧
    tensor s t u v ![0,1,0,1] =
      4*(5*(gram 0 s u*gram 0 t v)-gram 0 s t*gram 0 u v-gram 0 s v*gram 0 t u) ∧
    tensor s t u v ![0,1,1,0] =
      4*(5*(gram 0 s v*gram 0 t u)-gram 0 s t*gram 0 u v-gram 0 s u*gram 0 t v) := by
  have ha := trace_ab s t u v
  have hb := trace_ac s t u v
  have hc := trace_ad s t u v
  conv at ha => lhs; arg 2; ext i; arg 2; ext j; rw [tensor_metric_form]
  conv at hb => lhs; arg 2; ext i; arg 2; ext j; rw [tensor_metric_form]
  conv at hc => lhs; arg 2; ext i; arg 2; ext j; rw [tensor_metric_form]
  obtain ⟨h0,h1,h2⟩ := trace_shape (tensor s t u v ![0,0,1,1])
    (tensor s t u v ![0,1,0,1]) (tensor s t u v ![0,1,1,0])
  rw [h0] at ha
  rw [h1] at hb
  rw [h2] at hc
  have cancel (z : GaussianInt) (hz : 72*z=0) : z=0 :=
    (mul_eq_zero.mp hz).resolve_left (by decide)
  refine ⟨sub_eq_zero.mp (cancel _ ?_),sub_eq_zero.mp (cancel _ ?_),
    sub_eq_zero.mp (cancel _ ?_)⟩
  · linear_combination 5*ha-hb-hc
  · linear_combination 5*hb-ha-hc
  · linear_combination 5*hc-ha-hb

private theorem wick_pair : ∀ i j : Fin 4,
    wick i*wick j*metric i j=delta i j := by decide +kernel

private theorem wick_ne_zero : ∀ i : Fin 4, wick i ≠ 0 := by decide +kernel

private theorem unwick_pair (i j k l : Fin 4) :
    wick i*wick j*wick k*wick l*(metric i j*metric k l) = delta i j*delta k l ∧
    wick i*wick j*wick k*wick l*(metric i k*metric j l) = delta i k*delta j l ∧
    wick i*wick j*wick k*wick l*(metric i l*metric j k) = delta i l*delta j k := by
  constructor
  · calc
      _ = (wick i*wick j*metric i j)*(wick k*wick l*metric k l) := by ring
      _ = _ := by rw [wick_pair,wick_pair]
  constructor
  · calc
      _ = (wick i*wick k*metric i k)*(wick j*wick l*metric j l) := by ring
      _ = _ := by rw [wick_pair,wick_pair]
  · calc
      _ = (wick i*wick l*metric i l)*(wick j*wick k*metric j k) := by ring
      _ = _ := by rw [wick_pair,wick_pair]

theorem transverse_moments (s t u v i j k l : Fin 4) :
    sumMoment 0 s t u v i j k l = expected 0 s t u v i j k l := by
  obtain ⟨hB,hC,hD⟩ := coefficients s t u v
  have ht := tensor_metric_form s t u v i j k l
  rw [hB,hC,hD,tensor_raw] at ht
  change (wick i*wick j*wick k*wick l)*sumMoment 0 s t u v i j k l = _ at ht
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (wick_ne_zero i) (wick_ne_zero j)) (wick_ne_zero k)) (wick_ne_zero l))
  calc
    _ = _ := ht
    _ = (wick i*wick j*wick k*wick l)*expected 0 s t u v i j k l := by
      obtain ⟨h0,h1,h2⟩ := unwick_pair i j k l
      unfold expected
      change _ = (wick i*wick j*wick k*wick l)*(4*_)
      linear_combination -(4*(5*(gram 0 s t*gram 0 u v)-gram 0 s u*gram 0 t v-gram 0 s v*gram 0 t u))*h0-
        (4*(5*(gram 0 s u*gram 0 t v)-gram 0 s t*gram 0 u v-gram 0 s v*gram 0 t u))*h1-
        (4*(5*(gram 0 s v*gram 0 t u)-gram 0 s t*gram 0 u v-gram 0 s u*gram 0 t v))*h2
end Math.HiggsFourWaveCubature.Structural.Transverse
