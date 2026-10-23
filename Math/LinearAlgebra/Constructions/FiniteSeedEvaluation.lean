import Mathlib.LinearAlgebra.Span.Basic

/-! Finite seed certificates reduce evaluated spans and linear vanishing tests.
Spanning is an explicit input; no invariant-theory generation is assumed. -/
namespace Math.FiniteSeedEvaluation
set_option autoImplicit false
section
variable {K R M V I : Type*} [Field K] [CommRing R]
  [AddCommGroup M] [Module R M] [Module K M]
  [AddCommGroup V] [Module K V]
  (seed : I → M) (span_seed : Submodule.span R (Set.range seed) = ⊤)
  (chi : R →+* K) (ev : M →ₗ[K] V)
  (compatible : ∀ r m, ev (r • m) = chi r • ev m)

include span_seed compatible in
/-- Evaluation preserves a complete seed span, even at nongeneric points. -/
theorem range_eq_span : LinearMap.range ev = Submodule.span K (Set.range (ev ∘ seed)) := by
  apply le_antisymm
  · rintro _ ⟨m,rfl⟩
    have hm : m ∈ Submodule.span R (Set.range seed) := by rw [span_seed]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      exact Submodule.subset_span ⟨i,rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [compatible]; exact Submodule.smul_mem _ _ hx
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨seed i,rfl⟩

include span_seed compatible in
/-- A linear target test vanishes on all evaluations iff it vanishes on seeds. -/
theorem test_zero_iff {W : Type*} [AddCommGroup W] [Module K W] (test : V →ₗ[K] W) :
    (∀ m, test (ev m) = 0) ↔ ∀ i, test (ev (seed i)) = 0 := by
  constructor
  · intro h i; exact h (seed i)
  · intro h m
    have hm : ev m ∈ Submodule.span K (Set.range (ev ∘ seed)) := by
      rw [← range_eq_span seed span_seed chi ev compatible]
      exact ⟨m,rfl⟩
    have hs : Submodule.span K (Set.range (ev ∘ seed)) ≤ LinearMap.ker test := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact h i
    exact hs hm

include span_seed in
/-- The identity evaluation gives an operator-level module-linear zero test. -/
theorem module_test_zero_iff {W : Type*} [AddCommGroup W] [Module R W]
    (test : M →ₗ[R] W) : (∀ m, test m = 0) ↔ ∀ i, test (seed i) = 0 := by
  constructor
  · intro h i; exact h (seed i)
  · intro h m
    have hs : Submodule.span R (Set.range seed) ≤ LinearMap.ker test := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact h i
    rw [span_seed] at hs
    exact hs (by trivial)
end
end Math.FiniteSeedEvaluation
