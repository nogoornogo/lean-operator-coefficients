import Math.LieGroups.E6.Minuscule.CompactRealForm

/-!
# Scalar commutant of the actual minuscule E6 matrices

Distinct Cartan weights force diagonality; a checked descending path to the
highest-weight coordinate forces the diagonal entries to agree. No abstract
irreducibility or supplied commutant certificate is assumed.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open TauCeti.E6Minuscule TauCeti.DynkinType
open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

theorem cartan_eq_diagonal (i : Fin 6) :
    cartan i = Matrix.diagonal (fun a => (e6MinusculeWeight a i : ℂ)) := by
  ext a b
  by_cases h : a = b
  · subst b
    simp [cartan]
  · simp [cartan, h]

theorem cartan_eq_lie (i : Fin 6) : cartan i = ⁅raising i, lowering i⁆ := by
  change TauCeti.matrixIntCastLieHom ℂ (cartanGeneratorMatrix i) = _
  rw [← isSerreSystem.lie_E_F_self i, (TauCeti.matrixIntCastLieHom ℂ).map_lie]
  rfl

/-- Each noninitial weight has a raising edge to a strictly earlier row. -/
theorem raising_predecessor (a : Fin 27) (ha : a ≠ 0) :
    ∃ b : Fin 27, ∃ i : Fin 6, b < a ∧ raisingMatrix i b a = 1 := by
  decide +kernel +revert

theorem offDiagonal_eq_zero_of_commute_cartan (M : Matrix27)
    (hH : ∀ i, Commute M (cartan i)) (a b : Fin 27) (hab : a ≠ b) : M a b = 0 := by
  by_contra hn
  apply hab
  apply e6MinusculeWeight_injective
  funext i
  have h := congrArg (fun X : Matrix27 => X a b) (hH i).eq
  rw [cartan_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  rw [mul_comm (M a b)] at h
  exact Int.cast_injective (mul_right_cancel₀ hn h).symm

theorem eq_diagonal_of_commute_cartan (M : Matrix27)
    (hH : ∀ i, Commute M (cartan i)) : M = Matrix.diagonal (fun a => M a a) := by
  ext a b
  by_cases h : a = b
  · subst b; simp
  · simp [h, offDiagonal_eq_zero_of_commute_cartan M hH a b h]

theorem diagonal_eq_of_raising_edge (M : Matrix27)
    (hH : ∀ i, Commute M (cartan i)) (hE : ∀ i, Commute M (raising i))
    (i : Fin 6) (a b : Fin 27) (he : raisingMatrix i a b = 1) : M a a = M b b := by
  have h := congrArg (fun X : Matrix27 => X a b) (hE i).eq
  conv_lhs at h => rw [eq_diagonal_of_commute_cartan M hH]
  conv_rhs at h => rw [eq_diagonal_of_commute_cartan M hH]
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  have he' : raising i a b = 1 := by
    change (raisingMatrix i a b : ℂ) = 1
    rw [he, Int.cast_one]
  simpa only [he', mul_one, one_mul] using h

theorem diagonal_constant (M : Matrix27)
    (hH : ∀ i, Commute M (cartan i)) (hE : ∀ i, Commute M (raising i))
    (a : Fin 27) : M a a = M 0 0 := by
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    by_cases ha : a = 0
    · subst a; rfl
    · obtain ⟨b, i, hba, he⟩ := raising_predecessor a ha
      exact (diagonal_eq_of_raising_edge M hH hE i b a he).symm.trans (ih b hba)

theorem commutant_scalar_of_cartan_raising (M : Matrix27)
    (hH : ∀ i, Commute M (cartan i)) (hE : ∀ i, Commute M (raising i)) :
    M = M 0 0 • (1 : Matrix27) := by
  ext a b
  by_cases h : a = b
  · subst b
    simpa using diagonal_constant M hH hE a
  · simp [h, offDiagonal_eq_zero_of_commute_cartan M hH a b h]

/-- Commutation with the twelve actual simple-root generators is sufficient. -/
theorem commutant_scalar_of_generators (M : Matrix27)
    (hE : ∀ i, Commute M (raising i)) (hF : ∀ i, Commute M (lowering i)) :
    M = M 0 0 • (1 : Matrix27) := by
  apply commutant_scalar_of_cartan_raising M _ hE
  intro i
  rw [cartan_eq_lie, Ring.lie_def]
  exact ((hE i).mul_right (hF i)).sub_right ((hF i).mul_right (hE i))

theorem matrixLieAlgebra_commutant_scalar (M : Matrix27)
    (hM : ∀ x ∈ matrixLieAlgebra ℂ, ⁅M, x⁆ = 0) :
    M = M 0 0 • (1 : Matrix27) := by
  apply commutant_scalar_of_generators
  · intro i
    exact sub_eq_zero.mp (hM _ (raising_mem_matrixLieAlgebra i))
  · intro i
    exact sub_eq_zero.mp (hM _ (lowering_mem_matrixLieAlgebra i))

theorem matrixLieAlgebra_commutant_iff (M : Matrix27) :
    (∀ x ∈ matrixLieAlgebra ℂ, ⁅M, x⁆ = 0) ↔ ∃ c : ℂ, M = c • (1 : Matrix27) := by
  constructor
  · intro hM
    exact ⟨M 0 0, matrixLieAlgebra_commutant_scalar M hM⟩
  · rintro ⟨c, rfl⟩ x _
    simp [Ring.lie_def]

end

end Math.E6.Minuscule
