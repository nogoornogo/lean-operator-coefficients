import Physics.StandardModel.Operators.CyclicBasisDipoleSelection

namespace GUT.CyclicSelectorDipoleSelection
set_option autoImplicit false
noncomputable section
open Math Representation CyclicWeightCoordinates CyclicBasisDipoleSelection
variable {k : ℕ} [NeZero k] {I J : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] (a : I → ZMod k) (b : J → ZMod k)
  (mu : I → ℂ) (ell : Module.Dual ℂ (J → ℂ))

/-- Coordinate support includes the actual selectors, not just charge overlap. -/
def SupportedMatch : Prop := ∃ i j, a i = b j ∧ mu i ≠ 0 ∧ ell (Pi.single j 1) ≠ 0

theorem coordinate_zero (f : IntertwiningMap (diagonal a) (diagonal b))
    (i : I) (j : J) (h : a i ≠ b j) : f (Pi.single i 1) j = 0 := by
  by_contra hn
  have he := (CyclicBasisDipoleSelection.selected_allowed_iff a b i j).mp
    ((DipoleFlavorSelection.allowed_iff _ _ _ _).mpr ⟨f,hn⟩)
  exact h he

/-- Finite coordinate expansion for arbitrary linear functionals. -/
theorem evaluation_expand (f : IntertwiningMap (diagonal a) (diagonal b)) :
    ell (f mu) = ∑ i, ∑ j, mu i * f (Pi.single i 1) j * ell (Pi.single j 1) := by
  have hm : mu = ∑ i, mu i • Pi.single i 1 := by ext t; simp [Pi.single_apply]
  have hx (x : J → ℂ) : x = ∑ j, x j • Pi.single j 1 := by ext t; simp [Pi.single_apply]
  calc
    ell (f mu) = ell (f (∑ i, mu i • Pi.single i 1)) := congrArg (fun x => ell (f x)) hm
    _ = ∑ i, mu i * ell (f (Pi.single i 1)) := by simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have he := congrArg ell (hx (f (Pi.single i 1)))
      simp only [map_sum,map_smul,smul_eq_mul] at he
      rw [he,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem selected_allowed_iff :
    (∃ c : DipoleFlavorSelection.Coefficients (diagonal a) (diagonal b),
      DipoleFlavorSelection.selector (diagonal a) (diagonal b) mu ell c ≠ 0) ↔
      SupportedMatch a b mu ell := by
  rw [DipoleFlavorSelection.allowed_iff]
  constructor
  · rintro ⟨f,hf⟩
    by_contra hn
    apply hf
    rw [evaluation_expand]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases hi : mu i = 0
    · simp [hi]
    by_cases hj : ell (Pi.single j 1) = 0
    · simp [hj]
    have hab : a i ≠ b j := fun h => hn ⟨i,j,h,hi,hj⟩
    simp [coordinate_zero a b f i j hab]
  · rintro ⟨i,j,h,hi,hj⟩
    refine ⟨matrixUnit a b i j h, ?_⟩
    have hm : matrixUnit a b i j h mu = mu i • Pi.single j 1 := by
      ext t
      simp [matrixUnit,Pi.single_apply]
    rw [hm,map_smul]
    exact mul_ne_zero hi hj

theorem selected_forbidden_iff :
    (∀ c : DipoleFlavorSelection.Coefficients (diagonal a) (diagonal b),
      DipoleFlavorSelection.selector (diagonal a) (diagonal b) mu ell c = 0) ↔
      ¬ SupportedMatch a b mu ell := by
  classical
  simpa using not_congr (selected_allowed_iff a b mu ell)

theorem zero_source_forbidden :
    ∀ c : DipoleFlavorSelection.Coefficients (diagonal a) (diagonal b),
      DipoleFlavorSelection.selector (diagonal a) (diagonal b) 0 ell c = 0 := by
  apply (selected_forbidden_iff a b 0 ell).mpr
  simp [SupportedMatch]

theorem zero_target_forbidden :
    ∀ c : DipoleFlavorSelection.Coefficients (diagonal a) (diagonal b),
      DipoleFlavorSelection.selector (diagonal a) (diagonal b) mu 0 c = 0 := by
  apply (selected_forbidden_iff a b mu 0).mpr
  simp [SupportedMatch]
end
end GUT.CyclicSelectorDipoleSelection
