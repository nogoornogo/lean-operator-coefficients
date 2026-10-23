import Math.Algebra.ScalarFourWaveCubature.Moments2

/-! Generated exact moment identities, checked by kernel reduction. -/
namespace Math.ScalarFourWaveCubature
set_option autoImplicit false

theorem moments30 : ∀ j k l : Fin 4, sumMoment 3 0 j k l = expected 3 0 j k l := by
  decide +kernel

theorem moments31 : ∀ j k l : Fin 4, sumMoment 3 1 j k l = expected 3 1 j k l := by
  decide +kernel

theorem moments32 : ∀ j k l : Fin 4, sumMoment 3 2 j k l = expected 3 2 j k l := by
  decide +kernel

theorem moments33 : ∀ j k l : Fin 4, sumMoment 3 3 j k l = expected 3 3 j k l := by
  decide +kernel

end Math.ScalarFourWaveCubature
