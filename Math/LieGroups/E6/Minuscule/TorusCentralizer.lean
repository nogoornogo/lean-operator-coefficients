import Math.LieGroups.E6.Minuscule.CubicTorusReconstruction
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! The actual six-circle subgroup is self-centralizing, hence maximal
among Abelian subgroups. No fundamental-group computation is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Math.E6.Minuscule.Torus

noncomputable section

open NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

theorem direction_single (i : Fin 6) (t : ℝ) :
    (direction (Pi.single i t) : Matrix27) = t • compactH i := by
  change (∑ j : Fin 6, (Pi.single i t : Fin 6 → ℝ) j • compactH j) = _
  simp [Pi.single_apply]

theorem centralizer_commutes_cartan (g : compactIdentityComponent)
    (hg : g ∈ Subgroup.centralizer (subgroup : Set compactIdentityComponent)) (i : Fin 6) :
    Commute (compactMatrix g) (cartan i) := by
  have he (t : ℝ) : compactMatrix g * exp (t • compactH i) =
      exp (t • compactH i) * compactMatrix g := by
    have hm : compactExp (direction (Pi.single i t)) ∈ subgroup :=
      ⟨phase (Pi.single i t), hom_phase _⟩
    have h := congrArg compactMatrix ((Subgroup.mem_centralizer_iff.mp hg) _ hm).symm
    simp only [compactMatrix_mul] at h
    have hx : compactMatrix (compactExp (direction (Pi.single i t))) = exp (t • compactH i) :=
      (compactExp_coe _).trans (congrArg exp (direction_single i t))
    rwa [hx] at h
  have hd : HasDerivAt (fun t : ℝ => exp (t • compactH i)) (compactH i) 0 := by
    simpa using hasDerivAt_exp_smul_const' (compactH i) (0 : ℝ)
  have hl := hd.const_mul (compactMatrix g)
  have hr := hd.mul_const (compactMatrix g)
  have hf := funext he
  rw [hf] at hl
  have hc : Commute (compactMatrix g) (compactH i) := hl.unique hr
  exact (Commute.smul_right_iff₀ Complex.I_ne_zero).mp hc

theorem centralizer_diagonal (g : compactIdentityComponent)
    (hg : g ∈ Subgroup.centralizer (subgroup : Set compactIdentityComponent)) :
    compactMatrix g = Matrix.diagonal (fun a => compactMatrix g a a) :=
  eq_diagonal_of_commute_cartan _ (centralizer_commutes_cartan g hg)

theorem diagonal_norm (g : compactIdentityComponent)
    (hd : compactMatrix g = Matrix.diagonal (fun a => compactMatrix g a a)) (a : Fin 27) :
    ‖compactMatrix g a a‖ = 1 := by
  have hu : star (compactMatrix g) * compactMatrix g = 1 := g.val.val.property.1.1
  rw [hd, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal] at hu
  have h := congrArg (fun M : Matrix27 => M a a) hu
  simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply] at h
  have hn := congrArg norm h
  simp only [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg (compactMatrix g a a)]

theorem mem_subgroup_of_diagonal (g : compactIdentityComponent)
    (hd : compactMatrix g = Matrix.diagonal (fun a => compactMatrix g a a)) : g ∈ subgroup := by
  let d : Fin 27 → Circle := fun a =>
    ⟨compactMatrix g a a, mem_sphere_zero_iff_norm.mpr (diagonal_norm g hd a)⟩
  exact ⟨recover d, (diagonal_reconstruction g d hd).symm⟩

theorem centralizer_eq : Subgroup.centralizer (subgroup : Set compactIdentityComponent) = subgroup := by
  apply le_antisymm
  · intro g hg
    exact mem_subgroup_of_diagonal g (centralizer_diagonal g hg)
  · rintro _ ⟨z, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨w, rfl⟩
    simpa only [map_mul] using congrArg hom (mul_comm w z)

theorem maximal_abelian (A : Subgroup compactIdentityComponent) (hT : subgroup ≤ A)
    (hA : ∀ g ∈ A, ∀ h ∈ A, Commute g h) : A = subgroup := by
  apply le_antisymm _ hT
  rw [← centralizer_eq]
  intro g hg
  exact fun h hh => (hA h (hT hh) g hg).eq

end

end Math.E6.Minuscule.Torus
