import Math.RepresentationTheory.Content.SpeciesPatternAssembly

/-! Normalized typed-pattern alternation with arbitrary module-valued output.
In particular the output may be a linear boson spectator, not only a scalar. -/
namespace Math.TypedPatternAlternation
set_option autoImplicit false
noncomputable section
variable {P : Type*} [DecidableEq P] {V : P → Type*}
  [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {N : Type*} [AddCommGroup N] [Module ℂ N] {n : ℕ}
  (pattern : Fin n → P)

def ordered (k : MultilinearMap ℂ (fun i => V (pattern i)) N) :
    MultilinearMap ℂ (fun _ : Fin n => ∀ s, V s) N :=
  k.compLinearMap (fun i => LinearMap.proj (pattern i))

def stabilizer : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun p => pattern ∘ p = pattern)

def Compatible (k : MultilinearMap ℂ (fun i => V (pattern i)) N) : Prop :=
  ∀ p : Equiv.Perm (Fin n), pattern ∘ p = pattern → ∀ w : Fin n → ∀ s, V s,
    Equiv.Perm.sign p • ordered pattern k (w ∘ p) = ordered pattern k w

def alternating (k : MultilinearMap ℂ (fun i => V (pattern i)) N) :
    (∀ s, V s) [⋀^Fin n]→ₗ[ℂ] N :=
  ((stabilizer pattern).card : ℂ)⁻¹ • (ordered pattern k).alternatization

theorem stabilizer_ne_zero : ((stabilizer pattern).card : ℂ) ≠ 0 := by
  have hm : (1 : Equiv.Perm (Fin n)) ∈ stabilizer pattern := by simp [stabilizer]
  exact_mod_cast (Finset.card_ne_zero.mpr ⟨1, hm⟩)

theorem alternating_pure (k : MultilinearMap ℂ (fun i => V (pattern i)) N)
    (hk : Compatible pattern k) (v : ∀ i, V (pattern i)) :
    alternating pattern k (fun i => Pi.single (pattern i) (v i)) = k v := by
  let w : Fin n → ∀ s, V s := fun i => Pi.single (pattern i) (v i)
  have ho : ordered pattern k w = k v := by simp [ordered, w]
  have ht (p : Equiv.Perm (Fin n)) :
      Equiv.Perm.sign p • ordered pattern k (w ∘ p) =
        if pattern ∘ p = pattern then k v else 0 := by
    by_cases hp : pattern ∘ p = pattern
    · rw [ite_eq_left hp, hk p hp, ho]
    · rw [ite_eq_right hp]
      obtain ⟨i, hi⟩ : ∃ i, pattern (p i) ≠ pattern i := by
        by_contra hn
        exact hp (funext (fun i => by simpa using not_exists.mp hn i))
      have hz : ordered pattern k (w ∘ p) = 0 := by
        apply k.map_coord_zero i
        exact Pi.single_eq_of_ne (Ne.symm hi) _
      rw [hz, smul_zero]
  simp only [alternating, AlternatingMap.smul_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]
  change ((stabilizer pattern).card : ℂ)⁻¹ •
    (∑ p, Equiv.Perm.sign p • ordered pattern k (w ∘ p)) = _
  simp_rw [ht]
  rw [← Finset.sum_filter]
  change ((stabilizer pattern).card : ℂ)⁻¹ • (∑ _p ∈ stabilizer pattern, k v) = _
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (stabilizer_ne_zero pattern), one_smul]

theorem alternating_vanish (k : MultilinearMap ℂ (fun i => V (pattern i)) N)
    (labels : Fin n → P) (v : ∀ i, V (labels i))
    (h : ¬ ∃ p : Equiv.Perm (Fin n), labels ∘ p = pattern) :
    alternating pattern k (fun i => Pi.single (labels i) (v i)) = 0 := by
  simp only [alternating, AlternatingMap.smul_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]
  suffices hz : (∑ p : Equiv.Perm (Fin n), Equiv.Perm.sign p •
      ordered pattern k (fun i => Pi.single (labels (p i)) (v (p i)))) = 0 by
    rw [hz, smul_zero]
  apply Finset.sum_eq_zero
  intro p _
  obtain ⟨i, hi⟩ : ∃ i, labels (p i) ≠ pattern i := by
    by_contra hn
    exact h ⟨p, funext (fun i => by simpa using not_exists.mp hn i)⟩
  have hz : ordered pattern k (fun i => Pi.single (labels (p i)) (v (p i))) = 0 := by
    apply k.map_coord_zero i
    exact Pi.single_eq_of_ne (Ne.symm hi) _
  rw [hz, smul_zero]

end
end Math.TypedPatternAlternation
