import Math.Algebra.HiggsFourWaveCubature.FlipData

/-! Kernel-checked coordinate-sign closure, including global phases. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
theorem flip_involutive2 (i : Fin 4) : ∀ a : Fin (count 2),
    flipIndex 2 i (flipIndex 2 i a) = a := by
  fin_cases i <;> decide +kernel
theorem flip_value2 (i : Fin 4) : ∀ a : Fin (count 2), ∀ s j : Fin 4,
    raw 2 (flipIndex 2 i a) s j = flipPhase 2 i a*sign i j*raw 2 a s j := by
  fin_cases i <;> decide +kernel
end Math.HiggsFourWaveCubature
