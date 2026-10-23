import Math.Algebra.Variational.VariationalIBP
import Math.RepresentationTheory.Jets.NonlinearJetIBP

/-! A two-sided differential equation closure for a possibly noncommutative
complex algebra. Divergences are added only as a linear relation range. -/
namespace Math.TwoSidedDifferential
set_option autoImplicit false
noncomputable section
variable {A I : Type*} [Ring A] [Algebra ℂ A]
  (D : I → A →ₗ[ℂ] A) (R : Set A)

inductive Generated : A → Prop
  | seed (p : A) : p ∈ R → Generated p
  | zero : Generated 0
  | add {p q : A} : Generated p → Generated q → Generated (p+q)
  | smul (c : ℂ) {p : A} : Generated p → Generated (c • p)
  | left (a : A) {p : A} : Generated p → Generated (a*p)
  | right (a : A) {p : A} : Generated p → Generated (p*a)
  | derivative (i : I) {p : A} : Generated p → Generated (D i p)

def relations : Submodule ℂ A where
  carrier := {p | Generated D R p}
  zero_mem' := Generated.zero
  add_mem' := Generated.add
  smul_mem' := Generated.smul

theorem seed_mem {p : A} (hp : p ∈ R) : p ∈ relations D R := Generated.seed p hp
theorem left_mem (a : A) {p : A} (hp : p ∈ relations D R) :
    a*p ∈ relations D R := Generated.left a hp
theorem right_mem (a : A) {p : A} (hp : p ∈ relations D R) :
    p*a ∈ relations D R := Generated.right a hp
theorem derivative_mem (i : I) {p : A} (hp : p ∈ relations D R) :
    D i p ∈ relations D R := Generated.derivative i hp

theorem minimal (T : Submodule ℂ A) (hR : R ⊆ T)
    (hL : ∀ a p, p ∈ T → a*p ∈ T) (hM : ∀ a p, p ∈ T → p*a ∈ T)
    (hD : ∀ i p, p ∈ T → D i p ∈ T) : relations D R ≤ T := by
  intro p hp
  induction hp with
  | seed p hp => exact hR hp
  | zero => exact T.zero_mem
  | add hp hq ihp ihq => exact T.add_mem ihp ihq
  | smul c hp ih => exact T.smul_mem c ih
  | left a hp ih => exact hL a _ ih
  | right a hp ih => exact hM a _ ih
  | derivative i hp ih => exact hD i _ ih

def combined : Submodule ℂ A := relations D R ⊔ (VariationalIBP.divergence D).range

theorem combined_seed {p : A} (hp : p ∈ R) : p ∈ combined D R :=
  Submodule.mem_sup_left (seed_mem D R hp)

theorem combined_divergence (c : I →₀ A) :
    VariationalIBP.divergence D c ∈ combined D R :=
  Submodule.mem_sup_right ⟨c, rfl⟩

end
end Math.TwoSidedDifferential

namespace Math.TwoSidedDifferential
set_option autoImplicit false
noncomputable section
variable {A I : Type*} [CommRing A] [Algebra ℂ A]
  (D : I → Derivation ℂ A A) (R : Set A)

theorem commutative_relations :
    relations (fun i => (D i).toLinearMap) R = DifferentialEquation.relations D R := by
  apply le_antisymm
  · apply minimal
    · exact fun _ hp => DifferentialEquation.seed_mem D R hp
    · exact fun a p hp => (DifferentialEquation.ideal D R).mul_mem_left a hp
    · exact fun a p hp => (DifferentialEquation.ideal D R).mul_mem_right a hp
    · exact fun i p hp => DifferentialEquation.stable D R i hp
  · intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨w, r, hr, rfl⟩ := hp
      induction w with
      | nil => exact seed_mem _ R hr
      | cons i w ih => exact derivative_mem _ R i ih
    | zero => exact Submodule.zero_mem _
    | add p q hp hq ihp ihq => exact Submodule.add_mem _ ihp ihq
    | smul a p hp ih => exact left_mem _ R a ih

theorem commutative_combined :
    combined (fun i => (D i).toLinearMap) R = DifferentialEquation.combined D R := by
  rw [combined, commutative_relations]
  rfl

end
end Math.TwoSidedDifferential
