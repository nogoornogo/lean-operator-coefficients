import Physics.StandardModel.Operators.QquePhysicalOrderedCompleteness
import Math.RepresentationTheory.FourSlotCoefficientEquiv
import Math.RepresentationTheory.FourSlotSpeciesTransport
import Math.LinearAlgebra.StatisticalCompleteness

open Math

/-! qque exterior completeness with arbitrary, possibly infinite-dimensional,
physical multiplicities. The remaining condition is symmetric quark flavor. -/
namespace GUT.QquePhysicalExteriorCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor QquePhysicalOrderedCompleteness SMEpsilonTensor
open scoped TensorProduct
variable {R Q U E : Type*} [Group R]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E]
  (q : Representation ℂ R Q) (u : Representation ℂ R U) (e : Representation ℂ R E)

local instance : AddCommGroup (((Color ⊗[ℂ] Weak) ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] Q) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] U) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((ℂ ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] E) :=
  Module.addCommMonoidToAddCommGroup ℂ

def Symmetric (k : Residual q u e) : Prop := ∀ x y z r,
  k ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] r)) =
    k ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] r))
abbrev OrderedSector := FourSlotCoefficientEquiv.antisymmetric
  (external quarkSpin q) (external upSpin u) (external electronSpin e)

theorem symmetric_of_ordered (k : Residual q u e)
    (hk : (homEquiv q u e).symm k ∈ OrderedSector q u e) : Symmetric q u e k := by
  intro x y z r
  have h := hk
    (((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] x)
    (((colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] y)
    ((colorBasis 2 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] z)
    (((1 : ℂ) ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] r)
  have h' := (assemble_apply q u e k (colorBasis 1) (colorBasis 0) (colorBasis 2)
    (weakBasis 1) (weakBasis 0) (weakBasis 1) (weakBasis 0)
    (weakBasis 0) (weakBasis 1) y x z r 1).symm.trans
    (h.trans (congrArg Neg.neg (assemble_apply q u e k
      (colorBasis 0) (colorBasis 1) (colorBasis 2) (weakBasis 0) (weakBasis 1)
      (weakBasis 0) (weakBasis 1) (weakBasis 0) (weakBasis 1) x y z r 1)))
  norm_num [eps2, eps3, colorBasis, weakBasis, Fin.ext_iff] at h'
  exact h'

theorem ordered_of_symmetric (k : Residual q u e) (hk : Symmetric q u e k) :
    (homEquiv q u e).symm k ∈ OrderedSector q u e := by
  apply (FourSlotCoefficientEquiv.mem_antisymmetric_iff _ _ _ _).mpr
  apply IntertwiningMap.ext
  repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
  rename_i a v s x b w t y c h z m j r
  change (homEquiv q u e).symm k
    (((((b ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ]
      (((a ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x)) ⊗ₜ[ℂ]
      (((c ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] ((m ⊗ₜ[ℂ] j) ⊗ₜ[ℂ] r))) =
    -(homEquiv q u e).symm k
    (((((a ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ]
      (((b ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ]
      (((c ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] ((m ⊗ₜ[ℂ] j) ⊗ₜ[ℂ] r)))
  rw [assemble_apply, assemble_apply, hk]
  simp only [eps2, eps3]
  ring

def residualSpace : Submodule ℂ (Residual q u e) where
  carrier := {k | Symmetric q u e k}
  zero_mem' := by intro x y z r; rfl
  add_mem' := by
    intro k l hk hl x y z r
    change k _ + l _ = k _ + l _
    rw [hk, hl]
  smul_mem' := by
    intro c k hk x y z r
    change c • k _ = c • k _
    rw [hk]

def sourceAction (_ : Unit) : Coefficient q u e →ₗ[ℂ] Coefficient q u e where
  toFun f := f.comp (FourSlotCoefficientEquiv.swap
    (external quarkSpin q) (external upSpin u) (external electronSpin e)).toIntertwiningMap
  map_add' f g := by ext v; rfl
  map_smul' z f := by ext v; rfl

/-- The local contraction contributes -1 to the repeated-Q exchange. The
target acts on flavor inputs, rather than silently treating them as scalars. -/
def targetAction (_ : Unit) : Residual q u e →ₗ[ℂ] Residual q u e where
  toFun k := -(k.comp (FourSlotCoefficientEquiv.swap q u e).toIntertwiningMap)
  map_add' k m := by ext v; simp [add_comm]
  map_smul' z k := by ext v; simp [smul_eq_mul]

attribute [local irreducible] homEquiv targetAction

theorem reconstruct_permutation (j : Unit) (k : Residual q u e) :
    sourceAction q u e j ((homEquiv q u e).symm k) =
      (homEquiv q u e).symm (targetAction q u e j k) := by
  apply IntertwiningMap.ext
  repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
  rename_i a v s x b w t y c h z m r l
  change (homEquiv q u e).symm k
      (((((b ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ]
        (((a ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x)) ⊗ₜ[ℂ]
        (((c ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] ((m ⊗ₜ[ℂ] r) ⊗ₜ[ℂ] l))) = _
  refine (assemble_apply q u e k b a c w v t s h r y x z l m).trans ?_
  refine Eq.trans ?_
    (assemble_apply q u e (targetAction q u e j k) a b c v w s t h r x y z l m).symm
  simp [targetAction, FourSlotCoefficientEquiv.swap, eps2, eps3]
  ring

theorem permutation_compatible (j : Unit) (f : Coefficient q u e) :
    homEquiv q u e (sourceAction q u e j f) =
      targetAction q u e j (homEquiv q u e f) := by
  have hswap := reconstruct_permutation q u e j (homEquiv q u e f)
  rw [(homEquiv q u e).symm_apply_apply] at hswap
  apply (homEquiv q u e).symm.injective
  rw [(homEquiv q u e).symm_apply_apply]
  exact hswap

theorem permutation_statistics_iff (f : Coefficient q u e) :
    f ∈ OrderedSector q u e ↔ homEquiv q u e f ∈ residualSpace q u e := by
  have h := StatisticalCompleteness.statistics_iff (homEquiv q u e)
    (sourceAction q u e) (targetAction q u e) (fun _ => (-1 : ℂ))
    (permutation_compatible q u e) f
  have hs : f ∈ OrderedSector q u e ↔
      f ∈ StatisticalCompleteness.sector (sourceAction q u e) (fun _ => (-1 : ℂ)) := by
    apply (FourSlotCoefficientEquiv.mem_antisymmetric_iff
      (external quarkSpin q) (external upSpin u) (external electronSpin e) f).trans
    change _ ↔ ∀ j : Unit, sourceAction q u e j f = (-1 : ℂ) • f
    simp only [sourceAction, LinearMap.coe_mk, AddHom.coe_mk, neg_one_smul]
    exact ⟨fun h _ => h, fun h => h ()⟩
  have ht (k : Residual q u e) : k ∈ residualSpace q u e ↔
      k ∈ StatisticalCompleteness.sector (targetAction q u e) (fun _ => (-1 : ℂ)) := by
    change Symmetric q u e k ↔ ∀ j : Unit, _
    simp only [targetAction, LinearMap.coe_mk, AddHom.coe_mk, neg_one_smul, neg_inj]
    constructor
    · intro hk j
      apply IntertwiningMap.ext
      ext x y z r
      exact hk x y z r
    · intro hk x y z r
      exact DFunLike.congr_fun (hk ()) ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] r))
  exact hs.trans (h.trans (ht _).symm)

def orderedEquiv : OrderedSector q u e ≃ₗ[ℂ] residualSpace q u e :=
  (ConstrainedCompleteness.Presentation.mk (homEquiv q u e)
    (permutation_statistics_iff q u e)).equiv

@[simp] theorem orderedEquiv_apply (f : OrderedSector q u e) :
    (orderedEquiv q u e f).val = homEquiv q u e f.val := rfl

@[simp] theorem orderedEquiv_symm_apply (k : residualSpace q u e) :
    ((orderedEquiv q u e).symm k).val = (homEquiv q u e).symm k.val := rfl

abbrev Sector := FourSlotSpeciesDegree.sector
  (external quarkSpin q) (external upSpin u) (external electronSpin e)

def exteriorEquiv : Sector q u e ≃ₗ[ℂ] residualSpace q u e :=
  (FourSlotCoefficientEquiv.equiv _ _ _).trans (orderedEquiv q u e)

def onFieldsEquiv {A B C : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    {a : Representation ℂ ((StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × R) A}
    {b : Representation ℂ ((StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × R) B}
    {c : Representation ℂ ((StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × R) C}
    (ea : Representation.Equiv a (external quarkSpin q))
    (eb : Representation.Equiv b (external upSpin u))
    (ec : Representation.Equiv c (external electronSpin e)) :
    FourSlotSpeciesDegree.sector a b c ≃ₗ[ℂ] residualSpace q u e :=
  (FourSlotSpeciesTransport.equiv ea eb ec).symm.trans (exteriorEquiv q u e)

end
end GUT.QquePhysicalExteriorCompleteness
