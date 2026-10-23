import Math.RepresentationTheory.Exterior.TypedPatternAlternation
import Math.RepresentationTheory.Symmetric.SymmetricMultilinearProjection

/-! Normalized symmetrization of a typed species pattern, with module-valued output. -/
namespace Math.TypedPatternSymmetrization
set_option autoImplicit false
noncomputable section
variable {P : Type*} [DecidableEq P] {V : P → Type*}
  [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {N : Type*} [AddCommGroup N] [Module ℂ N] {n : ℕ}
  (pattern : Fin n → P)

abbrev ordered := TypedPatternAlternation.ordered (V := V) (N := N) pattern
abbrev stabilizer := TypedPatternAlternation.stabilizer pattern

def Compatible (k : MultilinearMap ℂ (fun i => V (pattern i)) N) : Prop :=
  ∀ p : Equiv.Perm (Fin n), pattern ∘ p = pattern → ∀ w : Fin n → ∀ s, V s,
    ordered pattern k (w ∘ p) = ordered pattern k w

def symmetric (k : MultilinearMap ℂ (fun i => V (pattern i)) N) :
    SymmetricPowerDescent.symmetricMaps (A := ∀ s, V s) (N := N) n :=
  ⟨((stabilizer pattern).card : ℂ)⁻¹ •
      ∑ p : Equiv.Perm (Fin n),
        (MultilinearMap.domDomCongrLinearEquiv ℂ ℂ (∀ s, V s) N p) (ordered pattern k), by
    intro q w
    simp only [smul_apply, sum_apply, MultilinearMap.domDomCongrLinearEquiv_apply]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft q) _ _ (by intro p; rfl)⟩

def linear : MultilinearMap ℂ (fun i => V (pattern i)) N →ₗ[ℂ]
    SymmetricPowerDescent.symmetricMaps (A := ∀ s, V s) (N := N) n where
  toFun := symmetric pattern
  map_add' f h := by
    apply Subtype.ext
    ext w
    simp [symmetric, ordered, TypedPatternAlternation.ordered,
      Finset.sum_add_distrib, smul_add]
  map_smul' z f := by
    apply Subtype.ext
    ext w
    simp [symmetric, ordered, TypedPatternAlternation.ordered,
      Finset.smul_sum, smul_smul, mul_comm]

theorem symmetric_pure (k : MultilinearMap ℂ (fun i => V (pattern i)) N)
    (hk : Compatible pattern k) (v : ∀ i, V (pattern i)) :
    (symmetric pattern k).val (fun i => Pi.single (pattern i) (v i)) = k v := by
  let w : Fin n → ∀ s, V s := fun i => Pi.single (pattern i) (v i)
  have ho : ordered pattern k w = k v := by simp [ordered, TypedPatternAlternation.ordered, w]
  have ht (p : Equiv.Perm (Fin n)) :
      ordered pattern k (w ∘ p) = if pattern ∘ p = pattern then k v else 0 := by
    by_cases hp : pattern ∘ p = pattern
    · rw [ite_eq_left hp, hk p hp, ho]
    · rw [ite_eq_right hp]
      obtain ⟨i, hi⟩ : ∃ i, pattern (p i) ≠ pattern i := by
        by_contra hn
        exact hp (funext (fun i => by simpa using not_exists.mp hn i))
      apply k.map_coord_zero i
      exact Pi.single_eq_of_ne (Ne.symm hi) _
  simp only [symmetric, smul_apply, sum_apply, MultilinearMap.domDomCongrLinearEquiv_apply]
  change ((stabilizer pattern).card : ℂ)⁻¹ •
    (∑ p : Equiv.Perm (Fin n), ordered pattern k (w ∘ p)) = _
  simp_rw [ht]
  rw [← Finset.sum_filter]
  change ((stabilizer pattern).card : ℂ)⁻¹ • (∑ _p ∈ stabilizer pattern, k v) = _
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (TypedPatternAlternation.stabilizer_ne_zero pattern), one_smul]

theorem symmetric_vanish (k : MultilinearMap ℂ (fun i => V (pattern i)) N)
    (labels : Fin n → P) (v : ∀ i, V (labels i))
    (h : ¬ ∃ p : Equiv.Perm (Fin n), labels ∘ p = pattern) :
    (symmetric pattern k).val (fun i => Pi.single (labels i) (v i)) = 0 := by
  simp only [symmetric, smul_apply, sum_apply, MultilinearMap.domDomCongrLinearEquiv_apply]
  change ((stabilizer pattern).card : ℂ)⁻¹ •
    (∑ p : Equiv.Perm (Fin n), ordered pattern k
      (fun i => Pi.single (labels (p i)) (v (p i)))) = 0
  suffices hz : (∑ p : Equiv.Perm (Fin n),
      ordered pattern k (fun i => Pi.single (labels (p i)) (v (p i)))) = 0 by
    rw [hz, smul_zero]
  apply Finset.sum_eq_zero
  intro p _
  obtain ⟨i, hi⟩ : ∃ i, labels (p i) ≠ pattern i := by
    by_contra hn
    exact h ⟨p, funext (fun i => by simpa using not_exists.mp hn i)⟩
  apply k.map_coord_zero i
  exact Pi.single_eq_of_ne (Ne.symm hi) _

end
end Math.TypedPatternSymmetrization
