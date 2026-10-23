import Math.Algebra.ScalarFourWaveCubature.Moments3

/-! Generated exact moment identities, checked by kernel reduction. -/
namespace Math.ScalarFourWaveCubature
set_option autoImplicit false

theorem moments40 : ∀ j k l : Fin 4, sumMoment 4 0 j k l = expected 4 0 j k l := by
  decide +kernel

theorem moments41 : ∀ j k l : Fin 4, sumMoment 4 1 j k l = expected 4 1 j k l := by
  decide +kernel

theorem moments42 : ∀ j k l : Fin 4, sumMoment 4 2 j k l = expected 4 2 j k l := by
  decide +kernel

theorem moments43 : ∀ j k l : Fin 4, sumMoment 4 3 j k l = expected 4 3 j k l := by
  decide +kernel

end Math.ScalarFourWaveCubature
