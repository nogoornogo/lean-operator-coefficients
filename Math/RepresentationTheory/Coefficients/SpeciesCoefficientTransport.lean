import Math.RepresentationTheory.Exterior.FiniteSpeciesExterior
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport
import Math.LinearAlgebra.Selection.ConstrainedCompleteness

/-! Species-wise actual/model identifications and transport of independently
supported exterior coefficients, for any finite species set and slot count. -/
namespace Math.SpeciesCoefficientTransport
set_option autoImplicit false
noncomputable section
open Representation
variable {S G : Type*} [Fintype S] [DecidableEq S] [Group G]
  {V W : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  (a : ∀ s, Representation ℂ G (V s)) (b : ∀ s, Representation ℂ G (W s))

/-- Only field identifications; no coefficient, nonzero or completeness premise. -/
abbrev Inputs := ∀ s, Representation.Equiv (a s) (b s)

def fieldsEquiv (input : Inputs a b) :
    Representation.Equiv (FiniteSpeciesExterior.representation a)
      (FiniteSpeciesExterior.representation b) where
  toLinearEquiv := LinearEquiv.piCongrRight (fun s => (input s).toLinearEquiv)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext s
    exact IntertwiningMap.isIntertwining _ _ (input s).toIntertwiningMap g (x s)

@[simp] theorem fieldsEquiv_single (input : Inputs a b) (s : S) (x : V s) :
    fieldsEquiv a b input (Pi.single s x) = Pi.single s (input s x) := by
  ext t
  change input t (Pi.single s x t) = Pi.single s (input s x) t
  by_cases h : t = s
  · subst t; simp
  · simp [Pi.single_eq_of_ne h]

def supported (n : ℕ) (allowed : (Fin n → S) → Prop) :
    Submodule ℂ (FiniteSpeciesExterior.Coefficient a n) where
  carrier := {f | ∀ labels, ¬ allowed labels → FiniteSpeciesExterior.restrict a f labels = 0}
  zero_mem' := by intro labels _; ext v; rfl
  add_mem' := by
    intro f g hf hg labels hn
    rw [FiniteSpeciesExterior.restrict_add, hf labels hn, hg labels hn, zero_add]
  smul_mem' := by
    intro z f hf labels hn
    rw [FiniteSpeciesExterior.restrict_smul, hf labels hn, smul_zero]

def pull {n : ℕ} (input : Inputs a b) (f : FiniteSpeciesExterior.Coefficient b n) :
    FiniteSpeciesExterior.Coefficient a n :=
  f.comp ((fieldsEquiv a b input).exteriorPower n).toIntertwiningMap

theorem pull_mem {n : ℕ} (input : Inputs a b) (allowed : (Fin n → S) → Prop)
    (f : supported b n allowed) : pull a b input f.val ∈ supported a n allowed := by
  intro labels hn
  ext v
  change f.val (((fieldsEquiv a b input).exteriorPower n)
    (exteriorPower.ιMulti ℂ n (fun i => Pi.single (labels i) (v i)))) = 0
  rw [Representation.Equiv.exteriorPower_apply_ιMulti]
  change f.val (exteriorPower.ιMulti ℂ n
    (fun i => fieldsEquiv a b input (Pi.single (labels i) (v i)))) = 0
  simp only [fieldsEquiv_single]
  exact congrArg (fun k => k (fun i => input (labels i) (v i))) (f.property labels hn)

theorem pull_symm {n : ℕ} (input : Inputs a b)
    (f : FiniteSpeciesExterior.Coefficient a n) :
    pull a b input (pull b a (fun s => (input s).symm) f) = f := by
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  ext v
  change f (((fieldsEquiv b a (fun s => (input s).symm)).exteriorPower n)
    (((fieldsEquiv a b input).exteriorPower n) (exteriorPower.ιMulti ℂ n v))) = _
  rw [Representation.Equiv.exteriorPower_apply_ιMulti,
    Representation.Equiv.exteriorPower_apply_ιMulti]
  apply congrArg f
  apply congrArg (exteriorPower.ιMulti ℂ n)
  funext i s
  exact (input s).toLinearEquiv.symm_apply_apply (v i s)

/-- Actual to model orientation, uniform across all slot counts. -/
def equiv (input : Inputs a b) (n : ℕ) (allowed : (Fin n → S) → Prop) :
    supported a n allowed ≃ₗ[ℂ] supported b n allowed where
  toFun f := ⟨pull b a (fun s => (input s).symm) f.val,
    pull_mem b a (fun s => (input s).symm) allowed f⟩
  invFun f := ⟨pull a b input f.val, pull_mem a b input allowed f⟩
  left_inv f := by apply Subtype.ext; exact pull_symm a b input f.val
  right_inv f := by apply Subtype.ext; exact pull_symm b a (fun s => (input s).symm) f.val
  map_add' f g := by apply Subtype.ext; ext x; rfl
  map_smul' z f := by apply Subtype.ext; ext x; rfl

/-- Local/exchange classification is proved separately, then transported. -/
def complete {C : Type*} [AddCommGroup C] [Module ℂ C]
    (input : Inputs a b) (n : ℕ) (allowed : (Fin n → S) → Prop)
    (classification : supported b n allowed ≃ₗ[ℂ] C) :
    supported a n allowed ≃ₗ[ℂ] C := (equiv a b input n allowed).trans classification

end
end Math.SpeciesCoefficientTransport
