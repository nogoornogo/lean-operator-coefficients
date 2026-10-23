import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! A small exact scalar row certificate, independent of any source encoding. -/
namespace Math.SevenScalarConstraints
set_option autoImplicit false

theorem zero (a b c d e f g : ℂ)
    (r0 : 108*a+168*b-192*c = 0) (r1 : 144*a-576*b+144*c = 0)
    (r2 : 108*d+84*e-192*f+84*g = 0) (r3 : 144*d-288*e+144*f-288*g = 0)
    (h1 : d+f+2*g = 0) (h2 : a+c+2*b = 0) (h3 : d+f+2*e = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · linear_combination (1/300 : ℂ)*r0+(23/10800 : ℂ)*r1+(1/3 : ℂ)*h2
  · linear_combination (-1/864 : ℂ)*r1+(1/6 : ℂ)*h2
  · linear_combination (-1/300 : ℂ)*r0+(1/5400 : ℂ)*r1+(1/3 : ℂ)*h2
  · linear_combination (1/300 : ℂ)*r2+(23/10800 : ℂ)*r3+(1/6 : ℂ)*h1+(1/6 : ℂ)*h3
  · linear_combination (-1/864 : ℂ)*r3+(-1/6 : ℂ)*h1+(1/3 : ℂ)*h3
  · linear_combination (-1/300 : ℂ)*r2+(1/5400 : ℂ)*r3+(1/6 : ℂ)*h1+(1/6 : ℂ)*h3
  · linear_combination (-1/864 : ℂ)*r3+(1/3 : ℂ)*h1+(-1/6 : ℂ)*h3

end Math.SevenScalarConstraints
