import Math.RepresentationTheory.Fields.Selection
import Math.RepresentationTheory.Jets.DerivativeInterface

/-! Field/source dictionaries retain the exact preimage of full relations.
The image theorem applies even to a noninjective source map. It asserts no
extension of selected coefficients to the full source. -/
namespace Math.DerivativeInterface.Input
set_option autoImplicit false
noncomputable section
open Representation
variable {H U V : Type*} [Group H] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup V] [Module ℂ V] (P : Input H U)
  {tau : Representation ℂ H V}

def pullAlong (f : IntertwiningMap tau P.action) : Input H V where
  action := tau
  relations := P.relations.comap f.toLinearMap
  stable g v hv := by
    change f (tau g v) ∈ P.relations
    rw [IntertwiningMap.isIntertwining]
    exact P.stable g hv

def pullCoefficient (f : IntertwiningMap tau P.action) :
    P.Coefficient →ₗ[ℂ] (P.pullAlong f).Coefficient where
  toFun q := ⟨q.val.comp f, fun _ hv => q.property hv⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pull_evaluation (f : IntertwiningMap tau P.action)
    (q : P.Coefficient) (v : V) : (P.pullCoefficient f q).val v = q.val (f v) := rfl

def imageProjection (f : IntertwiningMap tau P.action) : V →ₗ[ℂ] P.Source :=
  P.projection.comp f.toLinearMap

theorem image_kernel (f : IntertwiningMap tau P.action) :
    (P.imageProjection f).ker = (P.pullAlong f).relations := by
  rw [imageProjection, LinearMap.ker_comp, projection, Submodule.ker_mkQ]
  rfl

def imageEquiv (f : IntertwiningMap tau P.action) :
    (P.pullAlong f).Source ≃ₗ[ℂ] (P.imageProjection f).range :=
  (Submodule.quotEquivOfEq _ _ (P.image_kernel f).symm).trans
    (P.imageProjection f).quotKerEquivRange

@[simp] theorem imageEquiv_projection (f : IntertwiningMap tau P.action) (v : V) :
    (P.imageEquiv f ((P.pullAlong f).projection v)).val = P.projection (f v) := rfl

/-- An exact field dictionary gives an equivalence of coefficient spaces,
with no new relation premise: the factory takes the exact full preimage. -/
def pullEquiv (e : Equiv tau P.action) : P.Coefficient ≃ₗ[ℂ]
    (P.pullAlong e.toIntertwiningMap).Coefficient where
  toFun := P.pullCoefficient e.toIntertwiningMap
  invFun q := ⟨q.val.comp e.symm.toIntertwiningMap, by
    intro u hu
    apply q.property
    change e (e.symm u) ∈ P.relations
    exact (e.toLinearEquiv.apply_symm_apply u).symm ▸ hu⟩
  left_inv q := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro u
    exact congrArg q.val (e.toLinearEquiv.apply_symm_apply u)
  right_inv q := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    exact congrArg q.val (e.toLinearEquiv.symm_apply_apply v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pullEquiv_evaluation (e : Equiv tau P.action)
    (q : P.Coefficient) (v : V) : (P.pullEquiv e q).val v = q.val (e v) := rfl

theorem pullEquiv_roundtrip (e : Equiv tau P.action) (q : P.Coefficient) :
    (P.pullEquiv e).symm (P.pullEquiv e q) = q := (P.pullEquiv e).symm_apply_apply q

def selectedFields (S : Subrepresentation P.action) (e : Equiv tau S.toRepresentation) :=
  P.pullAlong ((FieldSelection.inclusion S).comp e.toIntertwiningMap)

@[simp] theorem selectedFields_relations (S : Subrepresentation P.action)
    (e : Equiv tau S.toRepresentation) : (P.selectedFields S e).relations =
    P.relations.comap (S.toSubmodule.subtype.comp e.toLinearMap) := rfl

def selectedCoefficientEquiv (S : Subrepresentation P.action)
    (e : Equiv tau S.toRepresentation) :
    (P.select S.toSubmodule S.apply_mem_toSubmodule).Coefficient ≃ₗ[ℂ]
      (P.selectedFields S e).Coefficient :=
  (P.select S.toSubmodule S.apply_mem_toSubmodule).pullEquiv e

@[simp] theorem selectedCoefficient_evaluation (S : Subrepresentation P.action)
    (e : Equiv tau S.toRepresentation)
    (q : (P.select S.toSubmodule S.apply_mem_toSubmodule).Coefficient) (v : V) :
    (P.selectedCoefficientEquiv S e q).val v = q.val (e v) := rfl

end
end Math.DerivativeInterface.Input
