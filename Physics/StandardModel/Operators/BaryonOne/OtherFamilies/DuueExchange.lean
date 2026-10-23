import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuueOrderedCompleteness
import Math.RepresentationTheory.Coefficients.FourSlotCoefficientEquiv
import Math.LinearAlgebra.Selection.StatisticalCompleteness

open Math

/-! The repeated-up exchange equations, expressed solely on residual Hom. -/
namespace Physics.DuueExchange
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor DuueOrderedCompleteness SMEpsilonTensor
open scoped TensorProduct
variable {R U D E : Type*} [Group R]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup D] [Module ℂ D]
  [AddCommGroup E] [Module ℂ E]
  (u : Representation ℂ R U) (d : Representation ℂ R D) (e : Representation ℂ R E)

local instance : AddCommGroup ((Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] U) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] D) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((ℂ ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] E) :=
  Module.addCommMonoidToAddCommGroup ℂ

def Condition (k : Fin 2 → Residual u d e) : Prop := ∀ (x y : U) (h : D) (j : E),
  k 1 ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) = k 1 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) ∧
  k 0 ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) + k 1 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) =
    -k 0 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j))

abbrev OrderedSector := FourSlotCoefficientEquiv.antisymmetric
  (external upSpin u) (external downSpin d) (external electronSpin e)

theorem condition_of_antisymmetric (k : Fin 2 → Residual u d e)
    (hk : (homEquiv u d e).symm k ∈ OrderedSector u d e) : Condition u d e k := by
  intro x y h j
  have h₀ := hk
    ((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] x)
    ((colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] y)
    ((colorBasis 2 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] h)
    (((1 : ℂ) ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] j)
  have h₁ := hk
    ((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] x)
    ((colorBasis 1 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] y)
    ((colorBasis 2 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] h)
    (((1 : ℂ) ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] j)
  have h₀' := (assemble_apply u d e k (colorBasis 1) (colorBasis 0) (colorBasis 2) 1
    (weakBasis 1) (weakBasis 0) (weakBasis 0) (weakBasis 1) y x h j).symm.trans
    (h₀.trans (congrArg Neg.neg (
    assemble_apply u d e k (colorBasis 0) (colorBasis 1) (colorBasis 2) 1
    (weakBasis 0) (weakBasis 1) (weakBasis 0) (weakBasis 1) x y h j)))
  have h₁' := (assemble_apply u d e k (colorBasis 1) (colorBasis 0) (colorBasis 2) 1
    (weakBasis 0) (weakBasis 0) (weakBasis 1) (weakBasis 1) y x h j).symm.trans
    (h₁.trans (congrArg Neg.neg (
    assemble_apply u d e k (colorBasis 0) (colorBasis 1) (colorBasis 2) 1
    (weakBasis 0) (weakBasis 0) (weakBasis 1) (weakBasis 1) x y h j)))
  norm_num [eps3, FourDoubletInvariant.eps, colorBasis, weakBasis, Fin.ext_iff] at h₀' h₁'
  constructor
  · exact h₁'
  · linear_combination h₀' - h₁'

theorem antisymmetric_of_condition (k : Fin 2 → Residual u d e)
    (hk : Condition u d e k) : (homEquiv u d e).symm k ∈ OrderedSector u d e := by
  apply (FourSlotCoefficientEquiv.mem_antisymmetric_iff _ _ _ _).mpr
  apply IntertwiningMap.ext
  repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
  rename_i a s x b t y c v h z w j
  change (homEquiv u d e).symm k
    ((((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] ((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x)) ⊗ₜ[ℂ]
      (((c ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] ((z ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] j))) =
    -(homEquiv u d e).symm k
    ((((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ]
      (((c ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] ((z ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] j)))
  rw [assemble_apply, assemble_apply]
  obtain ⟨h₁,h₀⟩ := hk x y h j
  have h₀' : k 0 ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) =
      -k 0 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) - k 1 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) := by
    linear_combination h₀
  rw [h₁,h₀']
  simp only [eps3, FourDoubletInvariant.eps]
  ring

theorem antisymmetric_iff (k : Fin 2 → Residual u d e) :
    (homEquiv u d e).symm k ∈ OrderedSector u d e ↔ Condition u d e k :=
  ⟨condition_of_antisymmetric u d e k, antisymmetric_of_condition u d e k⟩

/-- Only residual intertwining and explicit flavor exchange equations remain. -/
def residualSpace : Submodule ℂ (Fin 2 → Residual u d e) where
  carrier := {k | Condition u d e k}
  zero_mem' := by intro x y h j; simp
  add_mem' := by
    intro k l hk hl x y h j
    obtain ⟨hk1, hk0⟩ := hk x y h j
    obtain ⟨hl1, hl0⟩ := hl x y h j
    constructor
    · change k 1 _ + l 1 _ = k 1 _ + l 1 _; rw [hk1, hl1]
    · change k 0 _ + l 0 _ + (k 1 _ + l 1 _) = -(k 0 _ + l 0 _)
      linear_combination hk0 + hl0
  smul_mem' := by
    intro z k hk x y h j
    obtain ⟨hk1, hk0⟩ := hk x y h j
    constructor
    · change z * k 1 _ = z * k 1 _; rw [hk1]
    · change z * k 0 _ + z * k 1 _ = -(z * k 0 _)
      linear_combination z * hk0

def sourceAction (_ : Unit) : Coefficient u d e →ₗ[ℂ] Coefficient u d e where
  toFun f := f.comp (FourSlotCoefficientEquiv.swap
    (external upSpin u) (external downSpin d) (external electronSpin e)).toIntertwiningMap
  map_add' f g := by ext v; rfl
  map_smul' z f := by ext v; rfl

/-- Explicit color/Weyl exchange matrix, retaining the exchanged up flavors. -/
def targetAction (_ : Unit) : (Fin 2 → Residual u d e) →ₗ[ℂ] (Fin 2 → Residual u d e) where
  toFun k i := if i = 0 then
    (k 0 + k 1).comp (FourSlotCoefficientEquiv.swap u d e).toIntertwiningMap
    else -(k 1).comp (FourSlotCoefficientEquiv.swap u d e).toIntertwiningMap
  map_add' k m := by
    funext i
    fin_cases i
    · apply IntertwiningMap.ext; apply LinearMap.ext; intro v
      change k 0 _ + m 0 _ + (k 1 _ + m 1 _) = (k 0 _ + k 1 _) + (m 0 _ + m 1 _)
      ring
    · apply IntertwiningMap.ext; apply LinearMap.ext; intro v
      change -(k 1 _ + m 1 _) = -k 1 _ + -m 1 _
      ring
  map_smul' z k := by
    funext i
    fin_cases i
    · apply IntertwiningMap.ext; apply LinearMap.ext; intro v
      change z * k 0 _ + z * k 1 _ = z * (k 0 _ + k 1 _)
      ring
    · apply IntertwiningMap.ext; apply LinearMap.ext; intro v
      change -(z * k 1 _) = z * -k 1 _
      ring

attribute [local irreducible] homEquiv

theorem target_zero (j : Unit) (k : Fin 2 → Residual u d e) (x y : U) (h : D) (l : E) :
    targetAction u d e j k 0 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l)) =
      k 0 ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l)) +
        k 1 ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l)) := by
  simp only [targetAction, LinearMap.coe_mk, AddHom.coe_mk]
  rfl

theorem target_one (j : Unit) (k : Fin 2 → Residual u d e) (x y : U) (h : D) (l : E) :
    targetAction u d e j k 1 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l)) =
      -k 1 ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l)) := by
  simp only [targetAction, LinearMap.coe_mk, AddHom.coe_mk]
  rfl

theorem reconstruct_permutation (j : Unit) (k : Fin 2 → Residual u d e) :
    sourceAction u d e j ((homEquiv u d e).symm k) =
      (homEquiv u d e).symm (targetAction u d e j k) := by
  apply IntertwiningMap.ext
  repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
  rename_i a s x b t y c v h z w l
  change (homEquiv u d e).symm k
    ((((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] ((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x)) ⊗ₜ[ℂ]
      (((c ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] ((z ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] l))) = _
  refine (assemble_apply u d e k b a c z t s v w y x h l).trans ?_
  refine Eq.trans ?_
    (assemble_apply u d e (targetAction u d e j k) a b c z s t v w x y h l).symm
  rw [target_zero, target_one]
  simp only [FourDoubletInvariant.eps, eps3]
  ring

theorem permutation_compatible (j : Unit) (f : Coefficient u d e) :
    homEquiv u d e (sourceAction u d e j f) =
      targetAction u d e j (homEquiv u d e f) := by
  have h := reconstruct_permutation u d e j (homEquiv u d e f)
  rw [(homEquiv u d e).symm_apply_apply] at h
  apply (homEquiv u d e).symm.injective
  rw [(homEquiv u d e).symm_apply_apply]
  exact h

theorem permutation_statistics_iff (f : Coefficient u d e) :
    f ∈ OrderedSector u d e ↔ homEquiv u d e f ∈ residualSpace u d e := by
  have h := StatisticalCompleteness.statistics_iff (homEquiv u d e)
    (sourceAction u d e) (targetAction u d e) (fun _ => (-1 : ℂ))
    (permutation_compatible u d e) f
  have hs : f ∈ OrderedSector u d e ↔
      f ∈ StatisticalCompleteness.sector (sourceAction u d e) (fun _ => (-1 : ℂ)) := by
    apply (FourSlotCoefficientEquiv.mem_antisymmetric_iff
      (external upSpin u) (external downSpin d) (external electronSpin e) f).trans
    change _ ↔ ∀ j : Unit, sourceAction u d e j f = (-1 : ℂ) • f
    simp only [sourceAction, LinearMap.coe_mk, AddHom.coe_mk, neg_one_smul]
    exact ⟨fun h _ => h, fun h => h ()⟩
  have ht (k : Fin 2 → Residual u d e) : k ∈ residualSpace u d e ↔
      k ∈ StatisticalCompleteness.sector (targetAction u d e) (fun _ => (-1 : ℂ)) := by
    constructor
    · intro hk j
      funext i
      fin_cases i
      · apply IntertwiningMap.ext
        ext x y h l
        simp only [Pi.smul_apply, neg_one_smul]
        change k 0 ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l)) +
          k 1 ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l)) =
          -k 0 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l))
        rw [(hk x y h l).1]
        exact (hk x y h l).2
      · apply IntertwiningMap.ext
        ext x y h l
        simp only [Pi.smul_apply, neg_one_smul]
        change -k 1 ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l)) =
          -k 1 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l))
        rw [(hk x y h l).1]
    · intro hk x y h l
      have h0 := DFunLike.congr_fun (congrFun (hk ()) 0)
        ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l))
      have h1 := DFunLike.congr_fun (congrFun (hk ()) 1)
        ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l))
      simp only [target_zero, Pi.smul_apply, neg_one_smul] at h0
      simp only [target_one, Pi.smul_apply, neg_one_smul] at h1
      change -k 1 ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l)) =
        -k 1 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l)) at h1
      change k 0 ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l)) +
        k 1 ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l)) =
        -k 0 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] l)) at h0
      have h1' := neg_injective h1
      exact ⟨h1', by rw [h1'] at h0; exact h0⟩
  exact hs.trans (h.trans (ht _).symm)

def orderedEquiv : OrderedSector u d e ≃ₗ[ℂ] residualSpace u d e :=
  (ConstrainedCompleteness.Presentation.mk (homEquiv u d e)
    (permutation_statistics_iff u d e)).equiv

@[simp] theorem orderedEquiv_apply (f : OrderedSector u d e) :
    (orderedEquiv u d e f).val = homEquiv u d e f.val := rfl

@[simp] theorem orderedEquiv_symm_apply (k : residualSpace u d e) :
    ((orderedEquiv u d e).symm k).val = (homEquiv u d e).symm k.val := rfl

/-- Independently defined degree-(2,1,1) exterior coefficients. -/
abbrev Sector := FourSlotSpeciesDegree.sector
  (external upSpin u) (external downSpin d) (external electronSpin e)

/-- Complete duue classification, including exterior descent and both inverses. -/
def exteriorEquiv : Sector u d e ≃ₗ[ℂ] residualSpace u d e :=
  (FourSlotCoefficientEquiv.equiv _ _ _).trans (orderedEquiv u d e)

theorem exists_nonzero_iff : (∃ f : Sector u d e, f ≠ 0) ↔
    ∃ k : residualSpace u d e, k ≠ 0 := by
  let a := exteriorEquiv u d e
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨a f, fun h => hf (a.injective (h.trans a.map_zero.symm))⟩
  · rintro ⟨k, hk⟩
    exact ⟨a.symm k, fun h => hk (a.symm.injective (h.trans a.symm.map_zero.symm))⟩

end
end Physics.DuueExchange
