import Math.RepresentationTheory.Relations.LocalRelationHom
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! Divergence-range descent for a graded family of ordinary total derivatives.
Concrete jet packages must prove covariance for their actual derivatives. -/
namespace Math.GradedJetIBP
set_option autoImplicit false
noncomputable section
open Representation

variable {I : Type*} {V : ℕ → Type*}
  [∀ d, AddCommGroup (V d)] [∀ d, Module ℂ (V d)]
  (D : ∀ _i : I, ∀ d, V d →ₗ[ℂ] V (d + 1))

abbrev Current (I : Type*) (V : ℕ → Type*)
    [∀ d, AddCommGroup (V d)] (d : ℕ) := I →₀ V d

def divergence (d : ℕ) : Current I V d →ₗ[ℂ] V (d + 1) :=
  Finsupp.lsum ℂ (fun i => D i d)

@[simp] theorem divergence_single (d : ℕ) (i : I) (p : V d) :
    divergence D d (Finsupp.single i p) = D i d p := Finsupp.lsum_single ℂ _ i p

def relations (d : ℕ) : Submodule ℂ (V (d + 1)) := (divergence D d).range

theorem derivative_mem (d : ℕ) (i : I) (p : V d) : D i d p ∈ relations D d :=
  ⟨Finsupp.single i p, divergence_single D d i p⟩

theorem annihilates_iff {W : Type*} [AddCommGroup W] [Module ℂ W] (d : ℕ)
    (f : V (d + 1) →ₗ[ℂ] W) :
    relations D d ≤ f.ker ↔ ∀ i p, f (D i d p) = 0 := by
  constructor
  · intro h i p; exact h (derivative_mem D d i p)
  · intro h u hu
    obtain ⟨c, rfl⟩ := hu
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using f.ker.add_mem ha hb
    | single i p => rw [divergence_single]; exact h i p

variable {H : Type*} [Group H] (ρ : ∀ d, Representation ℂ H (V d))
  (cov : ∀ h i d p, ρ (d + 1) h (D i d p) = D i d (ρ d h p))

include cov in
theorem divergence_covariant (d : ℕ) (h : H) (c : Current I V d) :
    ρ (d + 1) h (divergence D d c) =
      divergence D d (Finsupp.mapRange.linearMap (ρ d h) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single i p =>
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, divergence_single]
    exact cov h i d p

include cov in
theorem stable (d : ℕ) :
    ∀ h, relations D d ≤ (relations D d).comap (ρ (d + 1) h) := by
  intro h u hu
  obtain ⟨c, rfl⟩ := hu
  exact ⟨Finsupp.mapRange.linearMap (ρ d h) c, (divergence_covariant D ρ cov d h c).symm⟩

abbrev quotient (d : ℕ) := (ρ (d + 1)).quotient (relations D d) (stable D ρ cov d)
abbrev Coefficient (d : ℕ) := RelationQuotient.vanishing
  (ρ (d + 1)) (trivial ℂ H ℂ) (relations D d)

def coefficientEquiv (d : ℕ) : Coefficient D ρ d ≃ₗ[ℂ]
    IntertwiningMap (quotient D ρ cov d) (trivial ℂ H ℂ) :=
  RelationQuotient.equiv _ _ _ (stable D ρ cov d)

@[simp] theorem coefficientEquiv_mk (d : ℕ) (f : Coefficient D ρ d) (p : V (d + 1)) :
    coefficientEquiv D ρ cov d f ((relations D d).mkQ p) = f.val p := rfl

@[simp] theorem coefficientEquiv_symm (d : ℕ)
    (f : IntertwiningMap (quotient D ρ cov d) (trivial ℂ H ℂ)) (p : V (d + 1)) :
    ((coefficientEquiv D ρ cov d).symm f).val p = f ((relations D d).mkQ p) := rfl

variable {G : Type*} [Group G] (a : ∀ d, Representation ℂ G (V d))
  (comm : ∀ d g h p, a d g (ρ d h p) = ρ d h (a d g p))

abbrev LocalCoefficient (d : ℕ) := LocalRelationHom.Input
  (a (d + 1)) (ρ (d + 1)) (trivial ℂ H ℂ) (relations D d)

abbrev residual (d : ℕ) := LocalRelationHom.residual
  (a (d + 1)) (ρ (d + 1)) (comm (d + 1)) (relations D d) (stable D ρ cov d)

def localEquiv (d : ℕ) : LocalCoefficient D ρ a d ≃ₗ[ℂ]
    IntertwiningMap (residual D ρ cov a comm d) (trivial ℂ H ℂ) :=
  LocalRelationHom.equiv _ _ _ (comm (d + 1)) _ (stable D ρ cov d)

@[simp] theorem localEquiv_mk (d : ℕ) (f : LocalCoefficient D ρ a d) (p : V (d + 1)) :
    localEquiv D ρ cov a comm d f ((LocalRelationHom.image (a (d + 1)) (relations D d)).mkQ
      ((LocalCoinvariantHom.relations (a (d + 1))).mkQ p)) = f.val.val p := rfl

@[simp] theorem localEquiv_symm (d : ℕ)
    (f : IntertwiningMap (residual D ρ cov a comm d) (trivial ℂ H ℂ)) (p : V (d + 1)) :
    ((localEquiv D ρ cov a comm d).symm f).val.val p =
      f ((LocalRelationHom.image (a (d + 1)) (relations D d)).mkQ
        ((LocalCoinvariantHom.relations (a (d + 1))).mkQ p)) := rfl

theorem local_forbidden_iff (d : ℕ) :
    (∀ f : LocalCoefficient D ρ a d, f = 0) ↔
      ∀ f : IntertwiningMap (residual D ρ cov a comm d) (trivial ℂ H ℂ), f = 0 := by
  constructor
  · intro h f
    exact (localEquiv D ρ cov a comm d).symm.injective
      ((h _).trans (localEquiv D ρ cov a comm d).symm.map_zero.symm)
  · intro h f
    exact (localEquiv D ρ cov a comm d).injective
      ((h _).trans (localEquiv D ρ cov a comm d).map_zero.symm)

theorem local_nonzero_iff (d : ℕ) :
    (∃ f : LocalCoefficient D ρ a d, f ≠ 0) ↔
      ∃ f : IntertwiningMap (residual D ρ cov a comm d) (trivial ℂ H ℂ), f ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨localEquiv D ρ cov a comm d f, fun h =>
      hf ((localEquiv D ρ cov a comm d).injective (h.trans (map_zero _).symm))⟩
  · rintro ⟨f, hf⟩
    exact ⟨(localEquiv D ρ cov a comm d).symm f, fun h =>
      hf ((localEquiv D ρ cov a comm d).symm.injective (h.trans (map_zero _).symm))⟩

end
end Math.GradedJetIBP
