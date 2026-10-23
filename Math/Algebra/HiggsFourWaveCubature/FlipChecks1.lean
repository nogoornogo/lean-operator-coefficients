import Math.Algebra.HiggsFourWaveCubature.FlipData

/-! Kernel-checked coordinate-sign closure, including global phases. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
theorem flip_involutive1 (i : Fin 4) : ∀ a : Fin (count 1),
    flipIndex 1 i (flipIndex 1 i a) = a := by
  fin_cases i <;> decide +kernel
theorem flip_value1 (i : Fin 4) : ∀ a : Fin (count 1), ∀ s j : Fin 4,
    raw 1 (flipIndex 1 i a) s j = flipPhase 1 i a*sign i j*raw 1 a s j := by
  fin_cases i <;> decide +kernel
end Math.HiggsFourWaveCubature
