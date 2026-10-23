import Physics.FieldTheory.Spinor.Weyl.FourSameWeylCompleteness

/-! The central minus identity acts as minus one on either Weyl chirality. -/
namespace Physics.WeylCentralParity
set_option autoImplicit false
noncomputable section
open WeylSpinor
open scoped Matrix

def minusIdentity : Group :=
  ⟨!![-1, 0; 0, -1], by norm_num [Matrix.det_fin_two]⟩

theorem action_minus (rightHanded : Bool) (v : Space) :
    FourSameWeylCompleteness.action rightHanded minusIdentity v = (-1 : ℂ) • v := by
  cases rightHanded
  · change left minusIdentity v = (-1 : ℂ) • v
    ext i
    fin_cases i <;> simp [left, minusIdentity, Matrix.toLin'_apply, Matrix.mulVec] <;> rfl
  · change right minusIdentity v = (-1 : ℂ) • v
    rw [right_apply]
    ext i
    fin_cases i <;> simp [minusIdentity, Matrix.mulVec, Matrix.map_apply]

end
end Physics.WeylCentralParity
