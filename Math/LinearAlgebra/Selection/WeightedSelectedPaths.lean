import Math.LinearAlgebra.Selection.SelectedCoefficientInputs

/-! Finite path synthesis with arbitrary, potentially nonlinear input weights. -/
namespace Math.WeightedSelectedPaths
set_option autoImplicit false
noncomputable section

variable {I X D E : Type*} [Fintype I]
  [AddCommGroup D] [Module ℂ D] [AddCommGroup E] [Module ℂ E]
  (P : D →ₗ[ℂ] E) (paths : I → D) (w : X → I → ℂ)

def synthesis (x : X) : D := ∑ i, w x i • paths i

theorem selected (x : X) :
    P (synthesis paths w x) = ∑ i, w x i • P (paths i) := by
  simp [synthesis]

theorem nonzero_iff (x : X) : P (synthesis paths w x) ≠ 0 ↔
    (∑ i, w x i • P (paths i)) ≠ 0 := by rw [selected]

/-- Controllability of individual paths, without linearity of the input domain. -/
def Isolates : Prop := ∀ i : I, ∃ x : X,
  w x i = 1 ∧ ∀ j, j ≠ i → w x j = 0

theorem selected_isolated (i : I) (x : X) (hi : w x i = 1)
    (hrest : ∀ j, j ≠ i → w x j = 0) :
    P (synthesis paths w x) = P (paths i) := by
  rw [selected, Finset.sum_eq_single i]
  · rw [hi, one_smul]
  · intro j _ hji
    rw [hrest j hji, zero_smul]
  · simp

theorem exists_nonzero_iff_path (hw : Isolates w) :
    (∃ x, P (synthesis paths w x) ≠ 0) ↔ ∃ i, P (paths i) ≠ 0 := by
  constructor
  · rintro ⟨x, hx⟩
    by_contra h
    have hz : ∀ i, P (paths i) = 0 := by simpa using h
    exact hx (by simp [selected, hz])
  · rintro ⟨i, hi⟩
    obtain ⟨x, hx, hrest⟩ := hw i
    exact ⟨x, by rw [selected_isolated P paths w i x hx hrest]; exact hi⟩

/-- Other paths may exist, but their selected contributions must vanish. -/
theorem nonzero_of_single_selected_path (i : I) (x : X)
    (hi : w x i ≠ 0) (hp : P (paths i) ≠ 0)
    (hrest : ∀ j, j ≠ i → w x j • P (paths j) = 0) :
    P (synthesis paths w x) ≠ 0 := by
  rw [selected, Finset.sum_eq_single i]
  · exact smul_ne_zero hi hp
  · intro j _ hji
    exact hrest j hji
  · simp

omit [Fintype I] in
/-- A nonlinear coordinate-square family still isolates every path. -/
theorem squares_isolate : Isolates (fun x : I → ℂ => fun i => (x i)^2) := by
  classical
  intro i
  refine ⟨fun j => if j = i then 1 else 0, ?_, ?_⟩
  · simp
  · intro j hji
    simp [hji]

/-- Two opposing paths cancel with weights one on both paths. -/
theorem cancellation (d : D) :
    P (synthesis (fun i : Fin 2 => if i = 0 then d else -d)
      (fun _ : Unit => fun _ => 1) ()) = 0 := by
  simp [synthesis, Fin.sum_univ_two]

theorem cancellation_paths_nonzero (d : D) (hd : P d ≠ 0) (i : Fin 2) :
    P (if i = 0 then d else -d) ≠ 0 := by
  split_ifs <;> simpa using hd

end
end Math.WeightedSelectedPaths
