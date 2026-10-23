import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlOrderedCompleteness
import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlExchange
import Math.RepresentationTheory.Relations.FourSlotTripleExchange
import Math.RepresentationTheory.Tensors.FourSlotTripleRestriction
import Math.RepresentationTheory.Tensors.FourSlotTripleTransport

open Math

/-! Complete physical qqql degree-(3,1) classification by an explicit
residual-Hom exchange kernel, without finite-dimensional flavor assumptions. -/
namespace Physics.QqqlExteriorCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor QqqlOrderedCompleteness SMEpsilonTensor
open scoped TensorProduct
variable {R Q L : Type*} [Group R] [AddCommGroup Q] [Module ℂ Q]
  [AddCommGroup L] [Module ℂ L]
  (q : Representation ℂ R Q) (l : Representation ℂ R L)

local instance : AddCommGroup (((Color ⊗[ℂ] Weak) ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] Q) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((Weak ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] L) :=
  Module.addCommMonoidToAddCommGroup ℂ

def curryCoordinates : (Fin 2 × Fin 2 → Residual q l) ≃ₗ[ℂ] QqqlExchange.Family q l where
  toFun k i j := k (i,j)
  invFun k ij := k ij.1 ij.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinates := (homEquiv q l).trans (curryCoordinates q l)

abbrev OrderedSector := FourSlotTripleRestriction.orderedSector
  (external quarkSpin q) (external leptonSpin l)

theorem condition_of_ordered (k : QqqlExchange.Family q l)
    (hk : (coordinates q l).symm k ∈ OrderedSector q l) : QqqlExchange.Condition q l k := by
  apply (QqqlExchange.antisymmetric_iff q l k).mp
  have ha := (FourSlotTripleAlternation.alternates_iff_adjacent _).mp hk
  intro a b c v w x y z h
  have h01 := ha.1 (((a ⊗ₜ[ℂ] v 0) ⊗ₜ[ℂ] w 0) ⊗ₜ[ℂ] x)
    (((b ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] w 1) ⊗ₜ[ℂ] y)
    (((c ⊗ₜ[ℂ] v 2) ⊗ₜ[ℂ] w 2) ⊗ₜ[ℂ] z)
    ((v 3 ⊗ₜ[ℂ] w 3) ⊗ₜ[ℂ] h)
  have h12 := ha.2 (((a ⊗ₜ[ℂ] v 0) ⊗ₜ[ℂ] w 0) ⊗ₜ[ℂ] x)
    (((b ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] w 1) ⊗ₜ[ℂ] y)
    (((c ⊗ₜ[ℂ] v 2) ⊗ₜ[ℂ] w 2) ⊗ₜ[ℂ] z)
    ((v 3 ⊗ₜ[ℂ] w 3) ⊗ₜ[ℂ] h)
  change (homEquiv q l).symm (fun ij => k ij.1 ij.2) _ =
    -(homEquiv q l).symm (fun ij => k ij.1 ij.2) _ at h01 h12
  rw [assemble_apply, assemble_apply] at h01 h12
  dsimp [QqqlExchange.contraction, QqqlExchange.values]
  unfold QqqlExchange.values
  constructor
  · simpa [Function.comp_def,
      Equiv.swap_apply_def, Fin.ext_iff] using h01
  · simpa [Function.comp_def,
      Equiv.swap_apply_def, Fin.ext_iff] using h12

theorem ordered_of_condition (k : QqqlExchange.Family q l)
    (hk : QqqlExchange.Condition q l k) : (coordinates q l).symm k ∈ OrderedSector q l := by
  have ha := (QqqlExchange.antisymmetric_iff q l k).mpr hk
  apply (FourSlotTripleAlternation.alternates_iff_comp _).mpr
  constructor
  all_goals
    repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
    rename_i a v0 s0 x b v1 s1 y c v2 s2 z v3 s3 h
  · change (homEquiv q l).symm (fun ij => k ij.1 ij.2)
      (((((b ⊗ₜ[ℂ] v1) ⊗ₜ[ℂ] s1) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ]
        (((a ⊗ₜ[ℂ] v0) ⊗ₜ[ℂ] s0) ⊗ₜ[ℂ] x)) ⊗ₜ[ℂ]
        ((((c ⊗ₜ[ℂ] v2) ⊗ₜ[ℂ] s2) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] ((v3 ⊗ₜ[ℂ] s3) ⊗ₜ[ℂ] h))) =
      -(homEquiv q l).symm (fun ij => k ij.1 ij.2)
      (((((a ⊗ₜ[ℂ] v0) ⊗ₜ[ℂ] s0) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ]
        (((b ⊗ₜ[ℂ] v1) ⊗ₜ[ℂ] s1) ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ]
        ((((c ⊗ₜ[ℂ] v2) ⊗ₜ[ℂ] s2) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] ((v3 ⊗ₜ[ℂ] s3) ⊗ₜ[ℂ] h)))
    rw [assemble_apply, assemble_apply]
    have he := (ha a b c ![v0,v1,v2,v3] ![s0,s1,s2,s3] x y z h).1
    dsimp [QqqlExchange.contraction, QqqlExchange.values] at he
    unfold QqqlExchange.values at he
    simpa [Function.comp_def, Equiv.swap_apply_def, Fin.ext_iff] using he
  · change (homEquiv q l).symm (fun ij => k ij.1 ij.2)
      (((((a ⊗ₜ[ℂ] v0) ⊗ₜ[ℂ] s0) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ]
        (((c ⊗ₜ[ℂ] v2) ⊗ₜ[ℂ] s2) ⊗ₜ[ℂ] z)) ⊗ₜ[ℂ]
        ((((b ⊗ₜ[ℂ] v1) ⊗ₜ[ℂ] s1) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] ((v3 ⊗ₜ[ℂ] s3) ⊗ₜ[ℂ] h))) =
      -(homEquiv q l).symm (fun ij => k ij.1 ij.2)
      (((((a ⊗ₜ[ℂ] v0) ⊗ₜ[ℂ] s0) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ]
        (((b ⊗ₜ[ℂ] v1) ⊗ₜ[ℂ] s1) ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ]
        ((((c ⊗ₜ[ℂ] v2) ⊗ₜ[ℂ] s2) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] ((v3 ⊗ₜ[ℂ] s3) ⊗ₜ[ℂ] h)))
    rw [assemble_apply, assemble_apply]
    have he := (ha a b c ![v0,v1,v2,v3] ![s0,s1,s2,s3] x y z h).2
    dsimp [QqqlExchange.contraction, QqqlExchange.values] at he
    unfold QqqlExchange.values at he
    simpa [Function.comp_def, Equiv.swap_apply_def, Fin.ext_iff] using he

def orderedEquiv : OrderedSector q l ≃ₗ[ℂ] QqqlExchange.residualSpace q l where
  toFun f := ⟨coordinates q l f.val, condition_of_ordered q l _
    (((coordinates q l).symm_apply_apply f.val).symm ▸ f.property)⟩
  invFun k := ⟨(coordinates q l).symm k.val, ordered_of_condition q l k.val k.property⟩
  left_inv f := by apply Subtype.ext; exact (coordinates q l).symm_apply_apply f.val
  right_inv k := by apply Subtype.ext; exact (coordinates q l).apply_symm_apply k.val
  map_add' f g := by apply Subtype.ext; exact map_add (coordinates q l) f.val g.val
  map_smul' c f := by apply Subtype.ext; exact map_smul (coordinates q l) c f.val

abbrev Sector := FourSlotTripleSector.sector (external quarkSpin q) (external leptonSpin l)

/-- The exterior sector is defined by species degree, not as a contraction image. -/
def exteriorEquiv : Sector q l ≃ₗ[ℂ] QqqlExchange.residualSpace q l :=
  (FourSlotTripleRestriction.equiv _ _).trans (orderedEquiv q l)

theorem exists_nonzero_iff : (∃ f : Sector q l, f ≠ 0) ↔
    ∃ k : QqqlExchange.residualSpace q l, k ≠ 0 := by
  let e := exteriorEquiv q l
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨e f, fun h => hf (e.injective (h.trans e.map_zero.symm))⟩
  · rintro ⟨k, hk⟩
    exact ⟨e.symm k, fun h => hk (e.symm.injective (h.trans e.symm.map_zero.symm))⟩

/-- Actual field carriers enter through supplied equivariant identifications. -/
def onFieldsEquiv {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B]
    {a : Representation ℂ (PhysicalGroup × R) A}
    {b : Representation ℂ (PhysicalGroup × R) B}
    (eq : Representation.Equiv a (external quarkSpin q))
    (el : Representation.Equiv b (external leptonSpin l)) :
    FourSlotTripleSector.sector a b ≃ₗ[ℂ] QqqlExchange.residualSpace q l :=
  (FourSlotTripleTransport.equiv eq el).symm.trans (exteriorEquiv q l)

end
end Physics.QqqlExteriorCompleteness
