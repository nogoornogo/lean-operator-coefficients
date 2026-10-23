import Math.Algebra.HiggsFourWaveCubature.Structural.CollinearData

namespace Math.HiggsFourWaveCubature.Structural
set_option autoImplicit false
set_option Elab.async false

theorem phase_four (p : Fin 4) : phase p ^ 4 = 1 := by
  fin_cases p <;> decide +kernel

theorem gramSign_square (a : Fin 72) : gramSign a ^ 2 = 1 := by
  unfold gramSign
  split <;> ring

theorem swap_index_involutive (m : Fin 6) :
    ∀ a : Fin 72, swapIndex m (swapIndex m a) = a := by
  fin_cases m <;> decide +kernel

theorem swap_nodes (m : Fin 6) : ∀ a : Fin 72, ∀ s i : Fin 4,
    euclid (swapIndex m a) s i =
      phase (swapPhase m a)*euclid a s (Equiv.swap (swapLeft m) (swapRight m) i) := by
  fin_cases m <;> decide +kernel

theorem had_index_involutive :
    ∀ a : Fin 72, hadamardIndex (hadamardIndex a) = a := by decide +kernel

theorem had_nodes : ∀ a : Fin 72, ∀ s : Fin 4,
    2*euclid (hadamardIndex a) s 0 =
      phase (hadamardPhase a)*(∑ i : Fin 4, euclid a s i) := by decide +kernel

theorem gram_covariant (s t : Fin 4) : ∀ a : Fin 72,
    (∑ i : Fin 4, euclid a s i*euclid a t i) = gramSign a*gram 1 s t := by
  fin_cases s <;> fin_cases t <;> decide +kernel
end Math.HiggsFourWaveCubature.Structural
