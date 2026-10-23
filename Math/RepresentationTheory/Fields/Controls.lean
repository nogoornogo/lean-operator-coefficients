import Math.RepresentationTheory.Fields.Interactions
import Math.RepresentationTheory.Fields.DerivativeConnection
import Math.RepresentationTheory.Jets.DerivativeSelectionCounterexample
import Mathlib.Tactic

/-! Structural counterexamples to one-sided exactness, unconditional symmetry,
commuting-selector and global coefficient-extension shortcuts. -/
namespace Math.FieldSelectionControls
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

abbrev neutral := Representation.trivial ℂ Unit ℂ
abbrev ambient := neutral.prod neutral
def allFields : Subrepresentation ambient := ⊤
def embed : IntertwiningMap neutral ambient := IntertwiningMap.inl ℂ neutral neutral
def extract : (ℂ × ℂ) →ₗ[ℂ] ℂ := LinearMap.fst ℂ ℂ ℂ

theorem left_inverse (v : ℂ) : extract (embed v) = v := rfl

theorem missing_component :
    ¬ ∀ v, v ∈ allFields → embed (extract v) = v := by
  intro h
  have hh := congrArg Prod.snd (h (0,1) (by trivial))
  exact zero_ne_one hh

def first : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  (LinearMap.inl ℂ ℂ ℂ).comp (LinearMap.fst ℂ ℂ ℂ)
def diagonal : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  (LinearMap.id.prod LinearMap.id).comp (LinearMap.fst ℂ ℂ ℂ)

theorem selectors_idempotent : first.comp first = first ∧ diagonal.comp diagonal = diagonal := by
  constructor <;> rfl

theorem selectors_not_commuting : first.comp diagonal ≠ diagonal.comp first := by
  intro h
  have hh := congrArg (fun f : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) => (f (1,0)).2) h
  exact zero_ne_one hh

def constraints : Bool → (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ)
  | false => first
  | true => diagonal
theorem constraints_covariant (j : Bool) (g : Unit) (v : ℂ × ℂ) :
    constraints j (ambient g v) = ambient g (constraints j v) := rfl
def common := FieldSelection.fixed ambient constraints constraints_covariant

theorem common_zero (v : ℂ × ℂ) : v ∈ common ↔ v = 0 := by
  constructor
  · intro hv
    have h := (FieldSelection.mem_fixed constraints constraints_covariant v).mp hv
    have hp := congrArg Prod.snd (h false)
    have hq := congrArg Prod.snd (h true)
    exact Prod.ext (hq.trans hp.symm) hp.symm
  · rintro rfl
    exact (FieldSelection.mem_fixed constraints constraints_covariant 0).mpr (fun j => map_zero _)

theorem product_range_not_common : LinearMap.range (first.comp diagonal) ≠ common.toSubmodule := by
  intro h
  have hm : (1,0) ∈ common.toSubmodule := by
    rw [← h]
    exact ⟨(1,0),rfl⟩
  have hh := congrArg Prod.fst ((common_zero (1,0)).mp hm)
  exact one_ne_zero hh

def phase : Representation ℂ ℂˣ ℂ where
  toFun g := (g : ℂ) • LinearMap.id
  map_one' := by apply LinearMap.ext; intro x; simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change ((g : ℂ) * (h : ℂ)) * x = (g : ℂ) * ((h : ℂ) * x)
    ring

theorem nonfixed_vacuum : ¬ ∀ g, phase g 1 = 1 := by
  intro h
  have hh := h (-1)
  change (-1 : ℂ) * 1 = 1 at hh
  norm_num at hh

theorem wrong_map_rejected : ¬ ∀ g x,
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ) ((Representation.trivial ℂ ℂˣ ℂ) g x) =
      phase g ((LinearMap.id : ℂ →ₗ[ℂ] ℂ) x) := by
  intro h
  exact nonfixed_vacuum (fun g => (h g 1).symm)

def neutralCoefficient : InvariantCoefficientTransport.Invariants neutral :=
  ⟨LinearMap.id, fun _ => rfl⟩
theorem neutral_nonzero : neutralCoefficient ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg (fun f : InvariantCoefficientTransport.Invariants neutral => f 1) h)

def fixedInsertion := FieldSelection.atVacuum
  (Representation.TensorProduct.lid ℂ neutral).toIntertwiningMap
  (1 : ℂ) (fun _ => rfl)

theorem fixedInsertion_nonzero : fixedInsertion 1 = 1 := by
  change (TensorProduct.lid ℂ ℂ) ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = 1
  simp

theorem extension_still_required : ¬ Function.Surjective
    (DerivativeSelectionCounterexample.input.restrict
      DerivativeSelectionCounterexample.line DerivativeSelectionCounterexample.line_stable) :=
  DerivativeSelectionCounterexample.restriction_not_surjective

end
end Math.FieldSelectionControls
