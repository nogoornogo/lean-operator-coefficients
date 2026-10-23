import Math.RepresentationTheory.Jets.DerivativeProhibition

/-! Unrestricted basis coordinates for a full derivative input. Coordinate
families need not have finite support; evaluation on each source vector does. -/
namespace Math.AllOrderDerivativeCoordinates
set_option autoImplicit false
noncomputable section
open Representation
variable {H U ι κ : Type*} [Group H] [AddCommGroup U] [Module ℂ U]

structure Presentation (P : DerivativeInterface.Input H U) where
  basis : Module.Basis ι ℂ U
  relation : κ → U
  relation_span : Submodule.span ℂ (Set.range relation) = P.relations

namespace Presentation
variable {P : DerivativeInterface.Input H U} (C : Presentation (ι := ι) (κ := κ) P)

def assemble : (ι → ℂ) ≃ₗ[ℂ] (U →ₗ[ℂ] ℂ) := C.basis.constr ℂ

@[simp] theorem assemble_basis (c : ι → ℂ) (i : ι) : C.assemble c (C.basis i) = c i :=
  C.basis.constr_basis ℂ c i

theorem assemble_apply (c : ι → ℂ) (u : U) :
    C.assemble c u = (C.basis.repr u).sum (fun i a => a*c i) := by
  simpa only [assemble, smul_eq_mul] using C.basis.constr_apply ℂ c u

def rows : Submodule ℂ (ι → ℂ) where
  carrier := {c | (∀ k, C.assemble c (C.relation k) = 0) ∧
    ∀ g i, C.assemble c (P.action g (C.basis i)) = c i}
  zero_mem' := by simp
  add_mem' hc hd := by
    constructor
    · intro k
      rw [map_add, LinearMap.add_apply, hc.1 k, hd.1 k, add_zero]
    · intro g i
      rw [map_add, LinearMap.add_apply, hc.2 g i, hd.2 g i]
      rfl
  smul_mem' a c hc := by
    constructor
    · intro k
      rw [map_smul, LinearMap.smul_apply, hc.1 k, smul_zero]
    · intro g i
      rw [map_smul, LinearMap.smul_apply, hc.2 g i]
      rfl

def encode (f : P.Coefficient) : C.rows := ⟨fun i => f.val (C.basis i), by
  have he : C.assemble (fun i => f.val (C.basis i)) = f.val.toLinearMap :=
    C.basis.ext (fun i => C.assemble_basis _ i)
  constructor
  · intro k
    rw [he]
    exact f.property (by rw [← C.relation_span]; exact Submodule.subset_span ⟨k,rfl⟩)
  · intro g i
    rw [he]
    exact f.val.isIntertwining _ _ g (C.basis i)⟩

theorem rows_annihilate (c : C.rows) {u : U} (hu : u ∈ P.relations) :
    C.assemble c.val u = 0 := by
  rw [← C.relation_span] at hu
  induction hu using Submodule.span_induction with
  | mem v hv => obtain ⟨k,rfl⟩ := hv; exact c.property.1 k
  | zero => exact map_zero _
  | add v w hv hw ihv ihw => rw [map_add,ihv,ihw,add_zero]
  | smul a v hv ih => rw [map_smul,ih,smul_zero]

def decode (c : C.rows) : P.Coefficient := ⟨{
  toLinearMap := C.assemble c.val
  isIntertwining' g := by
    apply C.basis.ext
    intro i
    change C.assemble c.val (P.action g (C.basis i)) = C.assemble c.val (C.basis i)
    rw [assemble_basis]
    exact c.property.2 g i }, fun _ hu => C.rows_annihilate c hu⟩

def equivalence : P.Coefficient ≃ₗ[ℂ] C.rows where
  toFun := C.encode
  invFun := C.decode
  left_inv f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    exact C.basis.ext (fun i => C.assemble_basis _ i)
  right_inv c := by
    apply Subtype.ext
    funext i
    exact C.assemble_basis _ i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem reconstruction (f : P.Coefficient) (u : U) :
    f.val u = (C.basis.repr u).sum (fun i a => a*(C.equivalence f).val i) := by
  have he := congrArg (fun q : P.Coefficient => q.val u) (C.equivalence.symm_apply_apply f)
  exact he.symm.trans (C.assemble_apply _ u)

theorem prescribed_iff (c : ι → ℂ) :
    (∃ f : P.Coefficient, ∀ i, f.val (C.basis i) = c i) ↔ c ∈ C.rows := by
  constructor
  · rintro ⟨f,hf⟩
    have he : (C.encode f).val = c := funext hf
    exact he ▸ (C.encode f).property
  · intro hc
    exact ⟨C.decode ⟨c,hc⟩, fun i => C.assemble_basis c i⟩

theorem forbidden_iff : DerivativeProhibition.Forbids P ↔
    SelectionCriteria.Forbidden C.rows := (SelectionCriteria.ofEquiv C.equivalence).forbidden

theorem allowed_iff : DerivativeProhibition.Allows P ↔
    SelectionCriteria.Allowed C.rows := (SelectionCriteria.ofEquiv C.equivalence).allowed

end Presentation
end
end Math.AllOrderDerivativeCoordinates
