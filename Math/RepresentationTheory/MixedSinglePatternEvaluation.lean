import Math.RepresentationTheory.MixedSinglePatternAssembly

/-! Evaluate normalized exterior assembly even when the initial ordered vertex
is not itself exchange-compatible. This is not a commuting-polynomial test. -/
namespace Math.MixedSinglePatternEvaluation
set_option autoImplicit false
noncomputable section
open Representation
variable {P Q G : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] [Group G]
  {V : P → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {W : Q → Type*} [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  (r : ∀ s, Representation ℂ G (V s)) (t : ∀ s, Representation ℂ G (W s))
  {n : ℕ} (pattern : Fin n → P) (scalar : Q)
  (k : MultilinearMap ℂ (fun i => V (pattern i)) (W scalar →ₗ[ℂ] ℂ))
  (hk : MixedSinglePatternAssembly.Invariant r t pattern scalar k)

theorem assembly_value (v : ∀ i, V (pattern i)) (w : W scalar) :
    MixedSinglePatternAssembly.assemble r t pattern scalar k hk
      (MixedWeightSupport.pure (fun i => Pi.single (pattern i) (v i))
        (fun _ : Fin 1 => Pi.single scalar w)) =
    ((TypedPatternAlternation.stabilizer pattern).card : ℂ)⁻¹ *
      ∑ p ∈ TypedPatternAlternation.stabilizer pattern,
        (Equiv.Perm.sign p : ℂ) *
          k (fun i => (Pi.single (pattern (p i)) (v (p i))) (pattern i)) w := by
  change (MixedSingleBosonDescent.orderedEquiv n).symm
    (MixedSinglePatternAssembly.orderedExtension pattern scalar k)
      (MixedWeightSupport.pure _ _) = _
  rw [MixedSingleBosonDescent.lift_apply]
  simp only [MixedSinglePatternAssembly.orderedExtension,
    TypedPatternAlternation.alternating, AlternatingMap.smul_apply,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Units.smul_def,
    ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
  simp only [TypedPatternAlternation.ordered, MultilinearMap.compLinearMap_apply,
    MixedSinglePatternAssembly.lifted, LinearMap.compMultilinearMap_apply,
    MixedSinglePatternAssembly.spectatorLift, LinearMap.coe_mk,
    LinearMap.proj_apply]
  congr 1
  unfold TypedPatternAlternation.stabilizer
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : pattern ∘ p = pattern
  · simp [hp]
  · simp only [hp, ite_false]
    obtain ⟨i, hi⟩ : ∃ i, pattern (p i) ≠ pattern i := by
      by_contra hn
      exact hp (funext (fun i => by simpa using not_exists.mp hn i))
    have hz : k (fun j => Pi.single (pattern (p j)) (v (p j)) (pattern j)) = 0 := by
      apply k.map_coord_zero i
      exact Pi.single_eq_of_ne (Ne.symm hi) _
    rw [hz]
    simp
end
end Math.MixedSinglePatternEvaluation
