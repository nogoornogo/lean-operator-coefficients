import Physics.FieldTheory.Jets.Lorentz.LorentzFiniteControls

/-! Finite necessary controls on pair-symmetric invariant rank-four tensors.
All constraints come from actual Lorentz group elements. -/
namespace Physics.LorentzRankFour
set_option autoImplicit false
noncomputable section
open Math LorentzFiniteControls LorentzDirections
abbrev Dir := JetDirections.Direction (Fin 4)
abbrev Tensor := Dir →ₗ[ℂ] Dir →ₗ[ℂ] Dir →ₗ[ℂ] Dir →ₗ[ℂ] ℂ

def component (b : Tensor) (i j k l : Fin 4) : ℂ := b (E i) (E j) (E k) (E l)
theorem component_apply (b : Tensor) (i j k l : Fin 4) :
    component b i j k l = b (E i) (E j) (E k) (E l) := rfl
def killed (i j k l : Fin 4) : Prop :=
  signsZ i*signsZ j*signsZ k*signsZ l = -1 ∨
  signsX i*signsX j*signsX k*signsX l = -1

variable (b : Tensor)
  (h : ∀ g u v w x, b (direction g u) (direction g v)
    (direction g w) (direction g x) = b u v w x)
  (hs : ∀ u v w x, b u v w x = b v u w x)

include h in
theorem killed_zero (i j k l : Fin 4) (hk : killed i j k l) : component b i j k l = 0 := by
  have hz := h flipZ (E i) (E j) (E k) (E l)
  have hx := h flipX (E i) (E j) (E k) (E l)
  simp only [flipZ_direction,flipX_direction,map_smul,LinearMap.smul_apply,
    smul_eq_mul] at hz hx
  rcases hk with hk | hk
  · have he : -(component b i j k l) = component b i j k l := by
      calc
        _ = (signsZ i*signsZ j*signsZ k*signsZ l)*component b i j k l := by rw [hk]; ring
        _ = _ := by simpa only [component,E,mul_comm,mul_left_comm,mul_assoc] using hz
    linear_combination (-1/2 : ℂ)*he
  · have he : -(component b i j k l) = component b i j k l := by
      calc
        _ = (signsX i*signsX j*signsX k*signsX l)*component b i j k l := by rw [hk]; ring
        _ = _ := by simpa only [component,E,mul_comm,mul_left_comm,mul_assoc] using hx
    linear_combination (-1/2 : ℂ)*he

def normalComponent (i j k l : Fin 4) : ℂ := by
  classical
  exact if killed i j k l then 0 else b (E (min i j)) (E (max i j)) (E k) (E l)

include h hs in
theorem normalize (i j k l : Fin 4) : component b i j k l = normalComponent b i j k l := by
  classical
  unfold normalComponent
  split_ifs with hk
  · exact killed_zero b h i j k l hk
  · by_cases hij : i ≤ j
    · simp only [min_eq_left hij,max_eq_right hij,component]
    · simpa only [min_eq_right (le_of_not_ge hij),max_eq_left (le_of_not_ge hij),component]
        using hs (E i) (E j) (E k) (E l)

end
end Physics.LorentzRankFour
