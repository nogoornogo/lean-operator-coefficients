import Physics.StandardModel.Operators.Weinberg.WeinbergResidualHom

/-! Normalized local interpretation of Li v2, page 38, Out[7]. -/
namespace Physics.LiWeinbergConvention
set_option autoImplicit false
noncomputable section
open SMEpsilonTensor

def paperLocal (x y h : Weak) (s t : WeylSpinor.Space) : ℂ :=
  eps2 x h * eps2 y h * eps2 s t

def polarizedLocal (x y : Weak) (h : Fin 2 → Weak)
    (s t : WeylSpinor.Space) : ℂ :=
  (eps2 x (h 0) * eps2 y (h 1) + eps2 x (h 1) * eps2 y (h 0)) / 2 * eps2 s t

theorem diagonal_local (x y h : Weak) (s t : WeylSpinor.Space) :
    polarizedLocal x y ![h,h] s t = paperLocal x y h s t := by
  simp [polarizedLocal, paperLocal]

theorem lepton_exchange (x y : Weak) (h : Fin 2 → Weak)
    (s t : WeylSpinor.Space) :
    polarizedLocal y x h t s = -polarizedLocal x y h s t := by
  simp only [polarizedLocal, eps2]
  ring

theorem higgs_exchange (x y h₀ h₁ : Weak) (s t : WeylSpinor.Space) :
    polarizedLocal x y ![h₁,h₀] s t = polarizedLocal x y ![h₀,h₁] s t := by
  simp only [polarizedLocal, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem mixed_probe : polarizedLocal (weakBasis 0) (weakBasis 1)
    ![weakBasis 0,weakBasis 1] (weakBasis 0) (weakBasis 1) = -(1 / 2 : ℂ) := by
  norm_num [polarizedLocal, eps2, weakBasis]

end
end Physics.LiWeinbergConvention
