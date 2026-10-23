import Math.Algebra.HiggsFourWaveCubature.Structural.SecondCollinear

/-! Exact ordered moments, derived from the structural second-collinear identity. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false

theorem moments2_0_0 : ∀ j k l : Fin 4,
    sumMoment 2 0 0 0 0 0 j k l = expected 2 0 0 0 0 0 j k l := by
  intro j k l
  exact Structural.SecondCollinear.second_collinear_moments 0 0 0 0 0 j k l

theorem moments2_0_1 : ∀ j k l : Fin 4,
    sumMoment 2 0 0 0 0 1 j k l = expected 2 0 0 0 0 1 j k l := by
  intro j k l
  exact Structural.SecondCollinear.second_collinear_moments 0 0 0 0 1 j k l

theorem moments2_0_2 : ∀ j k l : Fin 4,
    sumMoment 2 0 0 0 0 2 j k l = expected 2 0 0 0 0 2 j k l := by
  intro j k l
  exact Structural.SecondCollinear.second_collinear_moments 0 0 0 0 2 j k l

theorem moments2_0_3 : ∀ j k l : Fin 4,
    sumMoment 2 0 0 0 0 3 j k l = expected 2 0 0 0 0 3 j k l := by
  intro j k l
  exact Structural.SecondCollinear.second_collinear_moments 0 0 0 0 3 j k l

end Math.HiggsFourWaveCubature
