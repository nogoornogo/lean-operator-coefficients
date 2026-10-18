import Physics.StandardModel.Operators.DuueExchange
import Math.RepresentationTheory.FourSlotSpeciesTransport

open Math

/-! Solving the duue exchange equations leaves one unrestricted residual Hom,
not a symmetric-up Hom. -/
namespace GUT.DuueResidualCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor DuueOrderedCompleteness DuueExchange
open scoped TensorProduct
variable {R U D E : Type*} [Group R]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup D] [Module ℂ D]
  [AddCommGroup E] [Module ℂ E]
  (u : Representation ℂ R U) (d : Representation ℂ R D) (e : Representation ℂ R E)

def swap (k : Residual u d e) : Residual u d e :=
  k.comp (FourSlotCoefficientEquiv.swap u d e).toIntertwiningMap

@[simp] theorem swap_apply (k : Residual u d e) (x y : U) (h : D) (j : E) :
    swap u d e k ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) =
      k ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) := rfl

def complete (k : Residual u d e) : residualSpace u d e :=
  ⟨![k, -k - swap u d e k], by
    intro x y h j
    constructor
    · change -k ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) -
        k ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) =
        -k ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) -
        k ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j))
      ring
    · change k ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) +
        (-k ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) -
        k ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j))) =
        -k ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j))
      ring⟩

def residualEquiv : residualSpace u d e ≃ₗ[ℂ] Residual u d e where
  toFun k := k.val 0
  invFun := complete u d e
  left_inv k := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · apply IntertwiningMap.ext
      apply TensorProduct.ext
      apply TensorProduct.ext
      apply LinearMap.ext; intro x
      apply LinearMap.ext; intro y
      apply TensorProduct.ext
      apply LinearMap.ext; intro h
      apply LinearMap.ext; intro j
      change -k.val 0 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) -
        k.val 0 ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) =
        k.val 1 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j))
      obtain ⟨_, hk⟩ := k.property x y h j
      linear_combination -hk
  right_inv k := rfl
  map_add' k l := rfl
  map_smul' z k := rfl

/-- The complete repeated-species exterior sector is one unrestricted Hom. -/
def homEquiv : Sector u d e ≃ₗ[ℂ] Residual u d e :=
  (exteriorEquiv u d e).trans (residualEquiv u d e)

theorem exists_nonzero_iff : (∃ f : Sector u d e, f ≠ 0) ↔
    ∃ k : Residual u d e, k ≠ 0 := by
  let a := homEquiv u d e
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨a f, fun h => hf (a.injective (h.trans a.map_zero.symm))⟩
  · rintro ⟨k, hk⟩
    exact ⟨a.symm k, fun h => hk (a.symm.injective (h.trans a.symm.map_zero.symm))⟩

local instance : AddCommGroup ((SMEpsilonTensor.Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] U) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((SMEpsilonTensor.Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] D) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((ℂ ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] E) :=
  Module.addCommMonoidToAddCommGroup ℂ

variable {A B C : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
  (a : Representation ℂ ((StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × R) A)
  (b : Representation ℂ ((StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × R) B)
  (c : Representation ℂ ((StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × R) C)
  (ea : Representation.Equiv a (external upSpin u))
  (eb : Representation.Equiv b (external downSpin d))
  (ec : Representation.Equiv c (external electronSpin e))

/-- Actual fields are supplied by equivariant identifications, not by assuming
that an unknown coefficient is already in the contraction image. -/
def onFieldsEquiv : FourSlotSpeciesDegree.sector a b c ≃ₗ[ℂ] Residual u d e :=
  (FourSlotSpeciesTransport.equiv ea eb ec).symm.trans (homEquiv u d e)

end
end GUT.DuueResidualCompleteness
