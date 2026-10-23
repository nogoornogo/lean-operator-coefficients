import Math.Algebra.ScalarFourWaveCubature.Moments1

/-! Generated exact moment identities, checked by kernel reduction. -/
namespace Math.ScalarFourWaveCubature
set_option autoImplicit false

theorem moments20 : ∀ j k l : Fin 4, sumMoment 2 0 j k l = expected 2 0 j k l := by
  decide +kernel

theorem moments21 : ∀ j k l : Fin 4, sumMoment 2 1 j k l = expected 2 1 j k l := by
  decide +kernel

theorem moments22 : ∀ j k l : Fin 4, sumMoment 2 2 j k l = expected 2 2 j k l := by
  decide +kernel

theorem moments23 : ∀ j k l : Fin 4, sumMoment 2 3 j k l = expected 2 3 j k l := by
  decide +kernel

end Math.ScalarFourWaveCubature
