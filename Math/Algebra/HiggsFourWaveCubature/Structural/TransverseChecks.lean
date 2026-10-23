import Math.Algebra.HiggsFourWaveCubature.Structural.TransverseData

namespace Math.HiggsFourWaveCubature.Structural.Transverse
set_option autoImplicit false
set_option Elab.async false

theorem phase_four (p : Fin 4) : phase p ^ 4 = 1 := by
  fin_cases p <;> decide +kernel

theorem gramSign_square (a : Fin 288) : gramSign a ^ 2 = 1 := by
  unfold gramSign
  split <;> ring

theorem swap_index_involutive (m : Fin 6) :
    ∀ a : Fin 288, swapIndex m (swapIndex m a) = a := by
  fin_cases m <;> decide +kernel

theorem swap_nodes_0_0 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 0 a) 0 i =
      phase (swapPhase 0 a)*euclid a 0 (Equiv.swap (swapLeft 0) (swapRight 0) i) := by
  decide +kernel

theorem swap_nodes_0_1 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 0 a) 1 i =
      phase (swapPhase 0 a)*euclid a 1 (Equiv.swap (swapLeft 0) (swapRight 0) i) := by
  decide +kernel

theorem swap_nodes_0_2 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 0 a) 2 i =
      phase (swapPhase 0 a)*euclid a 2 (Equiv.swap (swapLeft 0) (swapRight 0) i) := by
  decide +kernel

theorem swap_nodes_0_3 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 0 a) 3 i =
      phase (swapPhase 0 a)*euclid a 3 (Equiv.swap (swapLeft 0) (swapRight 0) i) := by
  decide +kernel

theorem swap_nodes_1_0 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 1 a) 0 i =
      phase (swapPhase 1 a)*euclid a 0 (Equiv.swap (swapLeft 1) (swapRight 1) i) := by
  decide +kernel

theorem swap_nodes_1_1 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 1 a) 1 i =
      phase (swapPhase 1 a)*euclid a 1 (Equiv.swap (swapLeft 1) (swapRight 1) i) := by
  decide +kernel

theorem swap_nodes_1_2 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 1 a) 2 i =
      phase (swapPhase 1 a)*euclid a 2 (Equiv.swap (swapLeft 1) (swapRight 1) i) := by
  decide +kernel

theorem swap_nodes_1_3 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 1 a) 3 i =
      phase (swapPhase 1 a)*euclid a 3 (Equiv.swap (swapLeft 1) (swapRight 1) i) := by
  decide +kernel

theorem swap_nodes_2_0 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 2 a) 0 i =
      phase (swapPhase 2 a)*euclid a 0 (Equiv.swap (swapLeft 2) (swapRight 2) i) := by
  decide +kernel

theorem swap_nodes_2_1 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 2 a) 1 i =
      phase (swapPhase 2 a)*euclid a 1 (Equiv.swap (swapLeft 2) (swapRight 2) i) := by
  decide +kernel

theorem swap_nodes_2_2 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 2 a) 2 i =
      phase (swapPhase 2 a)*euclid a 2 (Equiv.swap (swapLeft 2) (swapRight 2) i) := by
  decide +kernel

theorem swap_nodes_2_3 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 2 a) 3 i =
      phase (swapPhase 2 a)*euclid a 3 (Equiv.swap (swapLeft 2) (swapRight 2) i) := by
  decide +kernel

theorem swap_nodes_3_0 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 3 a) 0 i =
      phase (swapPhase 3 a)*euclid a 0 (Equiv.swap (swapLeft 3) (swapRight 3) i) := by
  decide +kernel

theorem swap_nodes_3_1 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 3 a) 1 i =
      phase (swapPhase 3 a)*euclid a 1 (Equiv.swap (swapLeft 3) (swapRight 3) i) := by
  decide +kernel

theorem swap_nodes_3_2 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 3 a) 2 i =
      phase (swapPhase 3 a)*euclid a 2 (Equiv.swap (swapLeft 3) (swapRight 3) i) := by
  decide +kernel

theorem swap_nodes_3_3 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 3 a) 3 i =
      phase (swapPhase 3 a)*euclid a 3 (Equiv.swap (swapLeft 3) (swapRight 3) i) := by
  decide +kernel

theorem swap_nodes_4_0 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 4 a) 0 i =
      phase (swapPhase 4 a)*euclid a 0 (Equiv.swap (swapLeft 4) (swapRight 4) i) := by
  decide +kernel

theorem swap_nodes_4_1 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 4 a) 1 i =
      phase (swapPhase 4 a)*euclid a 1 (Equiv.swap (swapLeft 4) (swapRight 4) i) := by
  decide +kernel

theorem swap_nodes_4_2 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 4 a) 2 i =
      phase (swapPhase 4 a)*euclid a 2 (Equiv.swap (swapLeft 4) (swapRight 4) i) := by
  decide +kernel

theorem swap_nodes_4_3 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 4 a) 3 i =
      phase (swapPhase 4 a)*euclid a 3 (Equiv.swap (swapLeft 4) (swapRight 4) i) := by
  decide +kernel

theorem swap_nodes_5_0 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 5 a) 0 i =
      phase (swapPhase 5 a)*euclid a 0 (Equiv.swap (swapLeft 5) (swapRight 5) i) := by
  decide +kernel

theorem swap_nodes_5_1 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 5 a) 1 i =
      phase (swapPhase 5 a)*euclid a 1 (Equiv.swap (swapLeft 5) (swapRight 5) i) := by
  decide +kernel

theorem swap_nodes_5_2 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 5 a) 2 i =
      phase (swapPhase 5 a)*euclid a 2 (Equiv.swap (swapLeft 5) (swapRight 5) i) := by
  decide +kernel

theorem swap_nodes_5_3 : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex 5 a) 3 i =
      phase (swapPhase 5 a)*euclid a 3 (Equiv.swap (swapLeft 5) (swapRight 5) i) := by
  decide +kernel

theorem swap_nodes (m : Fin 6) : ∀ a : Fin 288, ∀ s i : Fin 4,
    euclid (swapIndex m a) s i =
      phase (swapPhase m a)*euclid a s (Equiv.swap (swapLeft m) (swapRight m) i) := by
  intro a s i
  fin_cases m <;> fin_cases s
  · exact swap_nodes_0_0 a i
  · exact swap_nodes_0_1 a i
  · exact swap_nodes_0_2 a i
  · exact swap_nodes_0_3 a i
  · exact swap_nodes_1_0 a i
  · exact swap_nodes_1_1 a i
  · exact swap_nodes_1_2 a i
  · exact swap_nodes_1_3 a i
  · exact swap_nodes_2_0 a i
  · exact swap_nodes_2_1 a i
  · exact swap_nodes_2_2 a i
  · exact swap_nodes_2_3 a i
  · exact swap_nodes_3_0 a i
  · exact swap_nodes_3_1 a i
  · exact swap_nodes_3_2 a i
  · exact swap_nodes_3_3 a i
  · exact swap_nodes_4_0 a i
  · exact swap_nodes_4_1 a i
  · exact swap_nodes_4_2 a i
  · exact swap_nodes_4_3 a i
  · exact swap_nodes_5_0 a i
  · exact swap_nodes_5_1 a i
  · exact swap_nodes_5_2 a i
  · exact swap_nodes_5_3 a i

theorem had_index_involutive :
    ∀ a : Fin 288, hadamardIndex (hadamardIndex a) = a := by decide +kernel

theorem had_nodes_0 : ∀ a : Fin 288,
    2*euclid (hadamardIndex a) 0 0 =
      phase (hadamardPhase a)*(∑ i : Fin 4, euclid a 0 i) := by decide +kernel

theorem had_nodes_1 : ∀ a : Fin 288,
    2*euclid (hadamardIndex a) 1 0 =
      phase (hadamardPhase a)*(∑ i : Fin 4, euclid a 1 i) := by decide +kernel

theorem had_nodes_2 : ∀ a : Fin 288,
    2*euclid (hadamardIndex a) 2 0 =
      phase (hadamardPhase a)*(∑ i : Fin 4, euclid a 2 i) := by decide +kernel

theorem had_nodes_3 : ∀ a : Fin 288,
    2*euclid (hadamardIndex a) 3 0 =
      phase (hadamardPhase a)*(∑ i : Fin 4, euclid a 3 i) := by decide +kernel

theorem had_nodes : ∀ a : Fin 288, ∀ s : Fin 4,
    2*euclid (hadamardIndex a) s 0 =
      phase (hadamardPhase a)*(∑ i : Fin 4, euclid a s i) := by
  intro a s
  fin_cases s
  · exact had_nodes_0 a
  · exact had_nodes_1 a
  · exact had_nodes_2 a
  · exact had_nodes_3 a

theorem gram_covariant_0_0 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 0 i*euclid a 0 i) = gramSign a*gram 0 0 0 := by
  decide +kernel

theorem gram_covariant_0_1 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 0 i*euclid a 1 i) = gramSign a*gram 0 0 1 := by
  decide +kernel

theorem gram_covariant_0_2 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 0 i*euclid a 2 i) = gramSign a*gram 0 0 2 := by
  decide +kernel

theorem gram_covariant_0_3 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 0 i*euclid a 3 i) = gramSign a*gram 0 0 3 := by
  decide +kernel

theorem gram_covariant_1_0 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 1 i*euclid a 0 i) = gramSign a*gram 0 1 0 := by
  decide +kernel

theorem gram_covariant_1_1 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 1 i*euclid a 1 i) = gramSign a*gram 0 1 1 := by
  decide +kernel

theorem gram_covariant_1_2 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 1 i*euclid a 2 i) = gramSign a*gram 0 1 2 := by
  decide +kernel

theorem gram_covariant_1_3 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 1 i*euclid a 3 i) = gramSign a*gram 0 1 3 := by
  decide +kernel

theorem gram_covariant_2_0 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 2 i*euclid a 0 i) = gramSign a*gram 0 2 0 := by
  decide +kernel

theorem gram_covariant_2_1 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 2 i*euclid a 1 i) = gramSign a*gram 0 2 1 := by
  decide +kernel

theorem gram_covariant_2_2 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 2 i*euclid a 2 i) = gramSign a*gram 0 2 2 := by
  decide +kernel

theorem gram_covariant_2_3 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 2 i*euclid a 3 i) = gramSign a*gram 0 2 3 := by
  decide +kernel

theorem gram_covariant_3_0 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 3 i*euclid a 0 i) = gramSign a*gram 0 3 0 := by
  decide +kernel

theorem gram_covariant_3_1 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 3 i*euclid a 1 i) = gramSign a*gram 0 3 1 := by
  decide +kernel

theorem gram_covariant_3_2 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 3 i*euclid a 2 i) = gramSign a*gram 0 3 2 := by
  decide +kernel

theorem gram_covariant_3_3 : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a 3 i*euclid a 3 i) = gramSign a*gram 0 3 3 := by
  decide +kernel

theorem gram_covariant (s t : Fin 4) : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a s i*euclid a t i) = gramSign a*gram 0 s t := by
  intro a
  fin_cases s <;> fin_cases t
  · exact gram_covariant_0_0 a
  · exact gram_covariant_0_1 a
  · exact gram_covariant_0_2 a
  · exact gram_covariant_0_3 a
  · exact gram_covariant_1_0 a
  · exact gram_covariant_1_1 a
  · exact gram_covariant_1_2 a
  · exact gram_covariant_1_3 a
  · exact gram_covariant_2_0 a
  · exact gram_covariant_2_1 a
  · exact gram_covariant_2_2 a
  · exact gram_covariant_2_3 a
  · exact gram_covariant_3_0 a
  · exact gram_covariant_3_1 a
  · exact gram_covariant_3_2 a
  · exact gram_covariant_3_3 a
end Math.HiggsFourWaveCubature.Structural.Transverse
