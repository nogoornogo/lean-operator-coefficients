import Math.Algebra.HiggsFourWaveCubature.FlipData

/-! Kernel-checked coordinate-sign closure, including global phases. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
theorem flip_involutive0 (i : Fin 4) : ∀ a : Fin (count 0),
    flipIndex 0 i (flipIndex 0 i a) = a := by
  fin_cases i <;> decide +kernel
theorem flip_value0 (i : Fin 4) : ∀ a : Fin (count 0), ∀ s j : Fin 4,
    raw 0 (flipIndex 0 i a) s j = flipPhase 0 i a*sign i j*raw 0 a s j := by
  fin_cases i <;> decide +kernel
end Math.HiggsFourWaveCubature
