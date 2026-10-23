import Math.Algebra.Jets.TwoSidedDifferentialRelations

/-! A normal form for the full two-sided differential closure. Arbitrary
algebra multipliers remain present; no finite truncation is assumed. -/
namespace Math.TwoSidedDifferential
set_option autoImplicit false
noncomputable section
variable {A I : Type*} [Ring A] [Algebra ℂ A]
  (D : I → A →ₗ[ℂ] A) (R : Set A)

def normalGenerators : Set A :=
  {p | ∃ (a b r : A) (w : List I), r ∈ R ∧ a * VariationalIBP.word D w r * b = p}

theorem normal_mem (a b r : A) (w : List I) (hr : r ∈ R) :
    a * VariationalIBP.word D w r * b ∈ relations D R := by
  apply right_mem D R b
  apply left_mem D R a
  induction w with
  | nil => exact seed_mem D R hr
  | cons i w ih => exact derivative_mem D R i ih

theorem relations_eq_span_normal
    (leibniz : ∀ i p q, D i (p*q) = D i p*q + p*D i q) :
    relations D R = Submodule.span ℂ (normalGenerators D R) := by
  let T := Submodule.span ℂ (normalGenerators D R)
  have hn (a b r : A) (w : List I) (hr : r ∈ R) :
      a * VariationalIBP.word D w r * b ∈ T :=
    Submodule.subset_span ⟨a,b,r,w,hr,rfl⟩
  apply le_antisymm
  · apply minimal
    · intro r hr
      simpa [VariationalIBP.word] using hn 1 1 r [] hr
    · intro a p hp
      induction hp using Submodule.span_induction with
      | mem p hp =>
        obtain ⟨u,v,r,w,hr,rfl⟩ := hp
        simpa only [mul_assoc] using hn (a*u) v r w hr
      | zero => simp
      | add p q hp hq ihp ihq => simpa only [mul_add] using T.add_mem ihp ihq
      | smul c p hp ih => simpa only [mul_smul_comm] using T.smul_mem c ih
    · intro a p hp
      induction hp using Submodule.span_induction with
      | mem p hp =>
        obtain ⟨u,v,r,w,hr,rfl⟩ := hp
        simpa only [mul_assoc] using hn u (v*a) r w hr
      | zero => simp
      | add p q hp hq ihp ihq => simpa only [add_mul] using T.add_mem ihp ihq
      | smul c p hp ih => simpa only [smul_mul_assoc] using T.smul_mem c ih
    · intro i p hp
      induction hp using Submodule.span_induction with
      | mem p hp =>
        obtain ⟨u,v,r,w,hr,rfl⟩ := hp
        rw [leibniz, leibniz, add_mul]
        exact T.add_mem (T.add_mem (hn (D i u) v r w hr)
          (hn u v r (i::w) hr)) (hn u (D i v) r w hr)
      | zero => simpa only [map_zero] using T.zero_mem
      | add p q hp hq ihp ihq => simpa only [map_add] using T.add_mem ihp ihq
      | smul c p hp ih => simpa only [map_smul] using T.smul_mem c ih
  · apply Submodule.span_le.mpr
    rintro p ⟨a,b,r,w,hr,rfl⟩
    exact normal_mem D R a b r w hr

/-- An exact annihilation criterion for all multipliers and all derivatives. -/
theorem annihilates_iff
    (leibniz : ∀ i p q, D i (p*q) = D i p*q + p*D i q)
    (f : A →ₗ[ℂ] ℂ) :
    (∀ p ∈ relations D R, f p = 0) ↔
      ∀ a b r w, r ∈ R → f (a * VariationalIBP.word D w r * b) = 0 := by
  constructor
  · intro h a b r w hr
    exact h _ (normal_mem D R a b r w hr)
  · intro h p hp
    have hs : Submodule.span ℂ (normalGenerators D R) ≤ f.ker := by
      apply Submodule.span_le.mpr
      rintro q ⟨a,b,r,w,hr,rfl⟩
      exact h a b r w hr
    rw [relations_eq_span_normal D R leibniz] at hp
    exact hs hp

end
end Math.TwoSidedDifferential
