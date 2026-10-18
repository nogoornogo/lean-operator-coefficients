import Math.RepresentationTheory.SignedRelationQuotient
import Mathlib.LinearAlgebra.Prod

/-! Sign and degenerate-input controls for relation quotient completeness. -/
namespace Math.SignedRelationControls
set_option autoImplicit false
noncomputable section
open Representation

abbrev input := Representation.trivial ℂ Unit (ℂ × ℂ)
abbrev output := Representation.trivial ℂ Unit ℂ

def swap : IntertwiningMap input input where
  toLinearMap := (LinearEquiv.prodComm ℂ ℂ ℂ).toLinearMap
  isIntertwining' _ := rfl

def boson : IntertwiningMap input output where
  toLinearMap := LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ
  isIntertwining' _ := rfl

def fermion : IntertwiningMap input output where
  toLinearMap := LinearMap.fst ℂ ℂ ℂ - LinearMap.snd ℂ ℂ ℂ
  isIntertwining' _ := rfl

theorem boson_admissible : boson ∈ StatisticalCompleteness.sector
    (SignedRelationQuotient.action input output (fun _ : Unit => swap)) (fun _ => 1) := by
  intro j
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  change u.2 + u.1 = (1 : ℂ) • (u.1 + u.2)
  simp [add_comm]

theorem fermion_admissible : fermion ∈ StatisticalCompleteness.sector
    (SignedRelationQuotient.action input output (fun _ : Unit => swap)) (fun _ => -1) := by
  intro j
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  change u.2 - u.1 = (-1 : ℂ) • (u.1 - u.2)
  simp only [neg_one_smul]
  ring

theorem boson_not_fermion : boson ∉ StatisticalCompleteness.sector
    (SignedRelationQuotient.action input output (fun _ : Unit => swap)) (fun _ => -1) := by
  intro h
  have he := congrArg (fun f : IntertwiningMap input output => f (1, 0)) (h ())
  change (0 : ℂ) + 1 = (-1 : ℂ) • ((1 : ℂ) + 0) at he
  norm_num at he

theorem fermion_not_boson : fermion ∉ StatisticalCompleteness.sector
    (SignedRelationQuotient.action input output (fun _ : Unit => swap)) (fun _ => 1) := by
  intro h
  have he := congrArg (fun f : IntertwiningMap input output => f (1, 0)) (h ())
  change (0 : ℂ) - 1 = (1 : ℂ) • ((1 : ℂ) - 0) at he
  norm_num at he

def bosonDescended := SignedRelationQuotient.equiv input output
  (fun _ : Unit => swap) (fun _ => 1) ⟨boson, boson_admissible⟩

def fermionDescended := SignedRelationQuotient.equiv input output
  (fun _ : Unit => swap) (fun _ => -1) ⟨fermion, fermion_admissible⟩

theorem bosonDescended_nonzero : bosonDescended ≠ 0 := by
  intro h
  have he := congrArg (fun f => f
    ((SignedRelationQuotient.relations input (fun _ : Unit => swap) (fun _ => (1 : ℂ))).mkQ
      (1, 0))) h
  change boson (1, 0) = 0 at he
  change (1 : ℂ) + 0 = 0 at he
  norm_num at he

theorem fermionDescended_nonzero : fermionDescended ≠ 0 := by
  intro h
  have he := congrArg (fun f => f
    ((SignedRelationQuotient.relations input (fun _ : Unit => swap) (fun _ => (-1 : ℂ))).mkQ
      (1, 0))) h
  change fermion (1, 0) = 0 at he
  change (1 : ℂ) - 0 = 0 at he
  norm_num at he

theorem incompatible_identity_quotient :
    SignedRelationQuotient.relations input
      (fun _ : Unit => IntertwiningMap.id input) (fun _ => (-1 : ℂ)) = ⊤ :=
  SignedRelationQuotient.identity_relations_top input (-1) (by norm_num)

end
end Math.SignedRelationControls
