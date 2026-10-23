import Physics.StandardModel.Operators.Dipole.DipoleFlavorSelection
import Math.RepresentationTheory.Weights.CyclicWeightCoordinates

namespace Physics.CyclicBasisDipoleSelection
set_option autoImplicit false
noncomputable section
open Math Representation CyclicWeightCoordinates
variable {k : ℕ} [NeZero k] {I J : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] (a : I → ZMod k) (b : J → ZMod k)
  (i : I) (j : J)

def matrixUnit (h : a i = b j) : IntertwiningMap (diagonal a) (diagonal b) where
  toLinearMap := (LinearMap.single ℂ (fun _ : J => ℂ) j).comp (LinearMap.proj i)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext t
    by_cases ht : t=j
    · subst t
      simp [diagonal_apply,h]
    · simp [diagonal_apply,ht]

omit [Fintype I] [Fintype J] in
theorem matrixUnit_selected (h : a i = b j) :
    (matrixUnit a b i j h (Pi.single i 1)) j = 1 := by simp [matrixUnit]

theorem selected_allowed_iff :
    (∃ c : DipoleFlavorSelection.Coefficients (diagonal a) (diagonal b),
      DipoleFlavorSelection.selector (diagonal a) (diagonal b)
        (Pi.single i 1) (LinearMap.proj j) c ≠ 0) ↔ a i = b j := by
  rw [DipoleFlavorSelection.allowed_iff]
  constructor
  · rintro ⟨f,hf⟩
    apply ZMod.injective_stdAddChar
    have he := IntertwiningMap.isIntertwining _ _ f (Multiplicative.ofAdd (1 : ZMod k)) (Pi.single i 1)
    have hb := congrArg (fun x => x j) he
    have ha : diagonal a (Multiplicative.ofAdd (1 : ZMod k)) (Pi.single i 1) =
        ZMod.stdAddChar (a i * 1) • Pi.single i 1 := by
      simpa [Pi.basisFun_apply] using
        (diagonal_basis a (Multiplicative.ofAdd (1 : ZMod k)) i)
    rw [ha,map_smul] at hb
    simp only [Pi.smul_apply,smul_eq_mul,diagonal_apply,mul_one] at hb
    apply mul_right_cancel₀ hf
    simpa using hb
  · intro h
    exact ⟨matrixUnit a b i j h, by change (matrixUnit a b i j h (Pi.single i 1)) j ≠ 0; rw [matrixUnit_selected]; exact one_ne_zero⟩

theorem selected_forbidden_iff :
    (∀ c : DipoleFlavorSelection.Coefficients (diagonal a) (diagonal b),
      DipoleFlavorSelection.selector (diagonal a) (diagonal b)
        (Pi.single i 1) (LinearMap.proj j) c = 0) ↔ a i ≠ b j := by
  classical
  simpa using not_congr (selected_allowed_iff a b i j)
end
end Physics.CyclicBasisDipoleSelection
