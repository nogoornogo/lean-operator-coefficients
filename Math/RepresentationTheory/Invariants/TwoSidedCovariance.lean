import Math.Algebra.Jets.TwoSidedDifferentialRelations

/-! Full two-sided differential closure is preserved by multiplicative
linear maps with covariant derivatives. No commutativity is assumed. -/
namespace Math.TwoSidedCovariance
set_option autoImplicit false
noncomputable section

theorem linear_two_mem {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (L : V →ₗ[ℂ] W) (T : Submodule ℂ W)
    (v x y : V) (a b : ℂ) (h : v = a • x+b • y)
    (hx : L x ∈ T) (hy : L y ∈ T) : L v ∈ T := by
  rw [h,map_add,map_smul,map_smul]
  exact T.add_mem (T.smul_mem _ hx) (T.smul_mem _ hy)

variable {A I : Type*} [Ring A] [Algebra ℂ A] [Fintype I]
  (D : I → A →ₗ[ℂ] A) (R : Set A) (f : A →ₗ[ℂ] A)
  (hM : ∀ p q, f (p*q) = f p*f q) (c : I → I → ℂ)
  (hD : ∀ i p, f (D i p) = ∑ j, c i j • D j (f p))

include hM hD in
theorem equations_stable
    (hR : ∀ p ∈ R, f p ∈ TwoSidedDifferential.relations D R) :
    TwoSidedDifferential.relations D R ≤
      (TwoSidedDifferential.relations D R).comap f := by
  intro p hp
  change f p ∈ TwoSidedDifferential.relations D R
  induction hp with
  | seed p hp => exact hR p hp
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add hp hq ihp ihq => rw [map_add]; exact Submodule.add_mem _ ihp ihq
  | smul a hp ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih
  | left a hp ih => rw [hM]; exact TwoSidedDifferential.left_mem _ _ _ ih
  | right a hp ih => rw [hM]; exact TwoSidedDifferential.right_mem _ _ _ ih
  | derivative i hp ih =>
    rw [hD]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (TwoSidedDifferential.derivative_mem _ _ j ih))

include hD in
theorem ibp_stable : (VariationalIBP.divergence D).range ≤
    (VariationalIBP.divergence D).range.comap f := by
  rintro _ ⟨v,rfl⟩
  change f (VariationalIBP.divergence D v) ∈ (VariationalIBP.divergence D).range
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
  | single i p =>
    rw [VariationalIBP.divergence_single,hD]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      ⟨Finsupp.single j (f p),VariationalIBP.divergence_single _ _ _⟩)

include hM hD in
theorem combined_stable
    (hR : ∀ p ∈ R, f p ∈ TwoSidedDifferential.relations D R) :
    TwoSidedDifferential.combined D R ≤
      (TwoSidedDifferential.combined D R).comap f := by
  apply sup_le
  · exact fun p hp => Submodule.mem_sup_left (equations_stable D R f hM c hD hR hp)
  · exact fun p hp => Submodule.mem_sup_right (ibp_stable D f c hD hp)
end
end Math.TwoSidedCovariance

namespace Math.TwoSidedDifferential
set_option autoImplicit false
noncomputable section
variable {A I : Type*} [Ring A] [Algebra ℂ A]
  (D : I → A →ₗ[ℂ] A) {R S : Set A}

theorem relations_eq_of_span (h : Submodule.span ℂ R = Submodule.span ℂ S) :
    relations D R = relations D S := by
  have forward {R S : Set A} (h : Submodule.span ℂ R ≤ Submodule.span ℂ S) :
      relations D R ≤ relations D S := by
    apply minimal D R
    · intro p hp
      exact (Submodule.span_le.mpr (fun _ hs => seed_mem D S hs))
        (h (Submodule.subset_span hp))
    · exact fun a p hp => left_mem D S a hp
    · exact fun a p hp => right_mem D S a hp
    · exact fun i p hp => derivative_mem D S i hp
  exact le_antisymm (forward h.le) (forward h.ge)
end
end Math.TwoSidedDifferential
