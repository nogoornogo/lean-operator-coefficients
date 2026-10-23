import Math.Algebra.HiggsFourWaveCubature.Structural.TransverseChecks

/-! The unchanged transverse nodes induce the required tensor symmetries. -/
namespace Math.HiggsFourWaveCubature.Structural.Transverse
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators

def tensor (s t u v : Fin 4) : Tensor := fun x =>
  ∑ a : Fin 288, euclid a s (x 0)*euclid a t (x 1)*
    euclid a u (x 2)*euclid a v (x 3)

theorem tensor_raw (s t u v : Fin 4) (x : Fin 4 → Fin 4) :
    tensor s t u v x = (wick (x 0)*wick (x 1)*wick (x 2)*wick (x 3))*
      sumMoment 0 s t u v (x 0) (x 1) (x 2) (x 3) := by
  unfold tensor euclid sumMoment
  change (∑ a : Fin 288, (wick (x 0)*raw 0 a s (x 0))*(wick (x 1)*raw 0 a t (x 1))*
    (wick (x 2)*raw 0 a u (x 2))*(wick (x 3)*raw 0 a v (x 3))) =
    (wick (x 0)*wick (x 1)*wick (x 2)*wick (x 3))*
      ∑ a : Fin 288, raw 0 a s (x 0)*raw 0 a t (x 1)*raw 0 a u (x 2)*raw 0 a v (x 3)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

private def swapEquiv (m : Fin 6) : Fin 288 ≃ Fin 288 where
  toFun := swapIndex m
  invFun := swapIndex m
  left_inv := swap_index_involutive m
  right_inv := swap_index_involutive m

private theorem tensor_swap_code (m : Fin 6) (s t u v : Fin 4)
    (x : Fin 4 → Fin 4) :
    tensor s t u v (fun n => Equiv.swap (swapLeft m) (swapRight m) (x n)) =
      tensor s t u v x := by
  have hs := Equiv.sum_comp (swapEquiv m)
    (fun a => euclid a s (x 0)*euclid a t (x 1)*
      euclid a u (x 2)*euclid a v (x 3))
  change (∑ a, euclid (swapIndex m a) s (x 0)*euclid (swapIndex m a) t (x 1)*
      euclid (swapIndex m a) u (x 2)*euclid (swapIndex m a) v (x 3)) =
    tensor s t u v x at hs
  calc
    _ = ∑ a : Fin 288, phase (swapPhase m a)^4*
      (euclid a s (Equiv.swap (swapLeft m) (swapRight m) (x 0))*
       euclid a t (Equiv.swap (swapLeft m) (swapRight m) (x 1))*
       euclid a u (Equiv.swap (swapLeft m) (swapRight m) (x 2))*
       euclid a v (Equiv.swap (swapLeft m) (swapRight m) (x 3))) := by
      simp only [phase_four,one_mul,tensor]
    _ = ∑ a, euclid (swapIndex m a) s (x 0)*euclid (swapIndex m a) t (x 1)*
        euclid (swapIndex m a) u (x 2)*euclid (swapIndex m a) v (x 3) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [swap_nodes,swap_nodes,swap_nodes,swap_nodes]
      ring
    _ = _ := hs

private theorem swap_codes : ∀ p q : Fin 4, p ≠ q →
    ∃ m : Fin 6, Equiv.swap p q = Equiv.swap (swapLeft m) (swapRight m) := by
  decide +kernel

theorem tensor_swap (s t u v p q : Fin 4) (x : Fin 4 → Fin 4) :
    tensor s t u v (fun n => Equiv.swap p q (x n)) = tensor s t u v x := by
  by_cases h : p=q
  · subst q
    simp only [Equiv.swap_self,Equiv.refl_apply]
  · obtain ⟨m,hm⟩ := swap_codes p q h
    rw [hm]
    exact tensor_swap_code m s t u v x

theorem tensor_off_pair (s t u v i j k l : Fin 4) (h : ¬Paired i j k l) :
    tensor s t u v ![i,j,k,l] = 0 := by
  rw [tensor_raw]
  change (wick i*wick j*wick k*wick l)*sumMoment 0 s t u v i j k l = 0
  rw [off_pair_zero 0 s t u v i j k l h,mul_zero]

private def hadEquiv : Fin 288 ≃ Fin 288 where
  toFun := hadamardIndex
  invFun := hadamardIndex
  left_inv := had_index_involutive
  right_inv := had_index_involutive

private def diagonalSum (s t u v : Fin 4) : GaussianInt :=
  ∑ a : Fin 288, (∑ i : Fin 4, euclid a s i)*
    (∑ j : Fin 4, euclid a t j)*(∑ k : Fin 4, euclid a u k)*
    (∑ l : Fin 4, euclid a v l)

private theorem four_sums (f g h q : Fin 4 → GaussianInt) :
    (∑ i, f i)*(∑ j, g j)*(∑ k, h k)*(∑ l, q l) =
      ∑ i, ∑ j, ∑ k, ∑ l, f i*g j*h k*q l := by
  calc
    _ = ∑ i, f i*(∑ j,g j)*(∑ k,h k)*(∑ l,q l) := by
      rw [Finset.sum_mul,Finset.sum_mul,Finset.sum_mul]
    _ = ∑ i, ∑ j, f i*g j*(∑ k,h k)*(∑ l,q l) := by
      apply Finset.sum_congr rfl
      intro i _
      conv_lhs => lhs; lhs; rw [Finset.mul_sum]
      rw [Finset.sum_mul,Finset.sum_mul]
    _ = ∑ i, ∑ j, ∑ k, f i*g j*h k*(∑ l,q l) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      conv_lhs => lhs; rw [Finset.mul_sum]
      rw [Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]

private theorem diagonalSum_expand (s t u v : Fin 4) :
    diagonalSum s t u v =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        tensor s t u v ![i,j,k,l] := by
  change (∑ a : Fin 288, (∑ i,euclid a s i)*(∑ j,euclid a t j)*
    (∑ k,euclid a u k)*(∑ l,euclid a v l)) =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        ∑ a : Fin 288, euclid a s i*euclid a t j*euclid a u k*euclid a v l
  simp_rw [four_sums]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

theorem tensor_hadamard (s t u v : Fin 4) :
    16*tensor s t u v ![0,0,0,0] =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        tensor s t u v ![i,j,k,l] := by
  have hs := Equiv.sum_comp hadEquiv
    (fun a => euclid a s 0*euclid a t 0*euclid a u 0*euclid a v 0)
  change (∑ a, euclid (hadamardIndex a) s 0*euclid (hadamardIndex a) t 0*
    euclid (hadamardIndex a) u 0*euclid (hadamardIndex a) v 0) =
    tensor s t u v ![0,0,0,0] at hs
  calc
    _ = ∑ a : Fin 288, (2*euclid (hadamardIndex a) s 0)*
      (2*euclid (hadamardIndex a) t 0)*(2*euclid (hadamardIndex a) u 0)*
      (2*euclid (hadamardIndex a) v 0) := by
      rw [←hs,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = diagonalSum s t u v := by
      unfold diagonalSum
      apply Finset.sum_congr rfl
      intro a _
      rw [had_nodes,had_nodes,had_nodes,had_nodes]
      calc
        _ = phase (hadamardPhase a)^4*((∑ i,euclid a s i)*
          (∑ j,euclid a t j)*(∑ k,euclid a u k)*(∑ l,euclid a v l)) := by ring
        _ = _ := by rw [phase_four,one_mul]
    _ = _ := diagonalSum_expand s t u v

theorem tensor_metric_form (s t u v i j k l : Fin 4) :
    tensor s t u v ![i,j,k,l] =
      tensor s t u v ![0,0,1,1]*delta i j*delta k l+
      tensor s t u v ![0,1,0,1]*delta i k*delta j l+
      tensor s t u v ![0,1,1,0]*delta i l*delta j k := by
  exact tensor_shape (tensor s t u v) (tensor_swap s t u v)
    (tensor_off_pair s t u v) (tensor_hadamard s t u v) i j k l
end Math.HiggsFourWaveCubature.Structural.Transverse
