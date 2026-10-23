import Math.Algebra.HiggsFourWaveCubature.Structural.SecondCollinear

/-! Exact ordered moments, derived from the structural second-collinear identity. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false

theorem moments2_1_0 : ∀ j k l : Fin 4,
    sumMoment 2 0 0 0 1 0 j k l = expected 2 0 0 0 1 0 j k l := by
  intro j k l
  exact Structural.SecondCollinear.second_collinear_moments 0 0 0 1 0 j k l

theorem moments2_1_1 : ∀ j k l : Fin 4,
    sumMoment 2 0 0 0 1 1 j k l = expected 2 0 0 0 1 1 j k l := by
  intro j k l
  exact Structural.SecondCollinear.second_collinear_moments 0 0 0 1 1 j k l

theorem moments2_1_2 : ∀ j k l : Fin 4,
    sumMoment 2 0 0 0 1 2 j k l = expected 2 0 0 0 1 2 j k l := by
  intro j k l
  exact Structural.SecondCollinear.second_collinear_moments 0 0 0 1 2 j k l

theorem moments2_1_3 : ∀ j k l : Fin 4,
    sumMoment 2 0 0 0 1 3 j k l = expected 2 0 0 0 1 3 j k l := by
  intro j k l
  exact Structural.SecondCollinear.second_collinear_moments 0 0 0 1 3 j k l

end Math.HiggsFourWaveCubature
