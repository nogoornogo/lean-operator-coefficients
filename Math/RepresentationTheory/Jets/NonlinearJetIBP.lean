import Math.Algebra.Jets.DifferentialEquationIdeal

/-! The actual divergence range after polynomial EOM equals off-shell EOM
plus divergence. This is a linear quotient, not an ideal of divergences. -/
namespace Math.DifferentialEquation
set_option autoImplicit false
noncomputable section

variable {A I : Type*} [CommRing A] [Algebra ℂ A]
  (D : I → Derivation ℂ A A) (R : Set A)

def divergence : (I →₀ A) →ₗ[ℂ] A := Finsupp.lsum ℂ (fun i => (D i).toLinearMap)

@[simp] theorem divergence_single (i : I) (p : A) :
    divergence D (Finsupp.single i p) = D i p := Finsupp.lsum_single _ _ _ _

def ibp : Submodule ℂ A := LinearMap.range (divergence D)

theorem derivative_mem_ibp (i : I) (p : A) : D i p ∈ ibp D :=
  ⟨Finsupp.single i p, divergence_single D i p⟩

theorem shell_ibp_map : ibp (derivative D R) = (ibp D).map (projection D R).toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    induction c using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using Submodule.zero_mem _
    | add c e hc he => simpa only [map_add] using Submodule.add_mem _ hc he
    | single i p =>
      obtain ⟨p, rfl⟩ := projection_surjective D R p
      rw [divergence_single, derivative_projection]
      exact ⟨_, derivative_mem_ibp D i p, rfl⟩
  · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    induction c using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using Submodule.zero_mem _
    | add c e hc he => simpa only [map_add] using Submodule.add_mem _ hc he
    | single i p =>
      rw [divergence_single]
      change projection D R (D i p) ∈ _
      rw [← derivative_projection]
      exact derivative_mem_ibp (derivative D R) i (projection D R p)

def combined : Submodule ℂ A := relations D R ⊔ ibp D

theorem combined_comap : combined D R = (ibp (derivative D R)).comap (projection D R).toLinearMap := by
  rw [shell_ibp_map, Submodule.comap_map_eq, linear_kernel, sup_comm]
  rfl

def combinedProjection : A →ₗ[ℂ] (Shell D R ⧸ ibp (derivative D R)) :=
  (ibp (derivative D R)).mkQ.comp (projection D R).toLinearMap

theorem combinedProjection_kernel : (combinedProjection D R).ker = combined D R := by
  rw [combinedProjection, LinearMap.ker_comp, Submodule.ker_mkQ, combined_comap]

theorem combinedProjection_surjective : Function.Surjective (combinedProjection D R) :=
  (ibp (derivative D R)).mkQ_surjective.comp (projection_surjective D R)

def sourceEquiv : (A ⧸ combined D R) ≃ₗ[ℂ] (Shell D R ⧸ ibp (derivative D R)) :=
  (Submodule.quotEquivOfEq _ _ (combinedProjection_kernel D R).symm).trans
    ((combinedProjection D R).quotKerEquivOfSurjective (combinedProjection_surjective D R))

@[simp] theorem sourceEquiv_mk (p : A) :
    sourceEquiv D R ((combined D R).mkQ p) =
      (ibp (derivative D R)).mkQ (projection D R p) := rfl

def coefficientEquiv {W : Type*} [AddCommGroup W] [Module ℂ W] :
    ((A ⧸ combined D R) →ₗ[ℂ] W) ≃ₗ[ℂ]
      ((Shell D R ⧸ ibp (derivative D R)) →ₗ[ℂ] W) :=
  LinearEquiv.arrowCongr (sourceEquiv D R) (LinearEquiv.refl ℂ W)

def integrated : A →ₗ[ℂ] (A ⧸ combined D R) := (combined D R).mkQ

theorem integrated_derivative (i : I) (p : A) : integrated D R (D i p) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_sup_right (derivative_mem_ibp D i p))

theorem integrated_equation {p : A} (hp : p ∈ ideal D R) : integrated D R p = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_sup_left hp)

theorem integration_by_parts (i : I) (p q : A) :
    integrated D R (p * D i q) = -integrated D R (q * D i p) := by
  have h := integrated_derivative D R i (p * q)
  rw [(D i).leibniz, map_add] at h
  exact eq_neg_of_add_eq_zero_left h

theorem ibp_map_stable [Fintype I] (f : A →ₐ[ℂ] A) (c : I → I → ℂ)
    (hD : ∀ i p, f (D i p) = ∑ j, c i j • D j (f p)) :
    ∀ p ∈ ibp D, f p ∈ ibp D := by
  rintro _ ⟨p, rfl⟩
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simpa only [map_add] using (ibp D).add_mem hp hq
  | single i p =>
    rw [divergence_single, hD]
    exact Submodule.sum_mem _ (fun j _ => (ibp D).smul_mem _ (derivative_mem_ibp D j _))

theorem combined_map_stable [Fintype I] (f : A →ₐ[ℂ] A)
    (hf : ∀ p ∈ ideal D R, f p ∈ ideal D R) (c : I → I → ℂ)
    (hD : ∀ i p, f (D i p) = ∑ j, c i j • D j (f p)) :
    combined D R ≤ (combined D R).comap f.toLinearMap := by
  apply sup_le
  · exact fun p hp => Submodule.mem_sup_left (hf p hp)
  · exact fun p hp => Submodule.mem_sup_right (ibp_map_stable D f c hD p hp)

def integratedTransport [Fintype I] (f : A →ₐ[ℂ] A)
    (hf : ∀ p ∈ ideal D R, f p ∈ ideal D R) (c : I → I → ℂ)
    (hD : ∀ i p, f (D i p) = ∑ j, c i j • D j (f p)) :
    (A ⧸ combined D R) →ₗ[ℂ] (A ⧸ combined D R) :=
  (combined D R).mapQ (combined D R) f.toLinearMap (combined_map_stable D R f hf c hD)

end
end Math.DifferentialEquation
