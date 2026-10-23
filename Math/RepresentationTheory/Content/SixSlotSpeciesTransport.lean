import Math.RepresentationTheory.Content.SixSlotSpeciesDegree
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport

/-! Species-preserving transport of the intrinsic six-field degree `(2,4)` sector. -/
namespace Math.SixSlotSpeciesTransport
set_option autoImplicit false
noncomputable section
open Representation SixSlotSpeciesDegree SplitRepresentationProjection

variable {H A B A' B' : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup A'] [Module ℂ A'] [AddCommGroup B'] [Module ℂ B']
  {a : Representation ℂ H A} {b : Representation ℂ H B}
  {a' : Representation ℂ H A'} {b' : Representation ℂ H B'}
  (ea : Representation.Equiv a a') (eb : Representation.Equiv b b')

def pull (f : coefficients a' b') : coefficients a b :=
  f.comp ((prodEquiv ea eb).exteriorPower 6).toIntertwiningMap

theorem scaling_commutes (r s : ℂ) :
    ((prodEquiv ea eb).exteriorPower 6).toIntertwiningMap.toLinearMap.comp
        ((scaling a b r s).exteriorPower 6).toLinearMap =
      ((scaling a' b' r s).exteriorPower 6).toLinearMap.comp
        ((prodEquiv ea eb).exteriorPower 6).toIntertwiningMap.toLinearMap := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    IntertwiningMap.toLinearMap_apply, Representation.Equiv.coe_toIntertwiningMap]
  change ((prodEquiv ea eb).exteriorPower 6)
      (((scaling a b r s).exteriorPower 6) (exteriorPower.ιMulti ℂ 6 v)) =
    ((scaling a' b' r s).exteriorPower 6)
      (((prodEquiv ea eb).exteriorPower 6) (exteriorPower.ιMulti ℂ 6 v))
  simp only [IntertwiningMap.exteriorPower_apply_ιMulti,
    Representation.Equiv.exteriorPower_apply_ιMulti]
  apply congrArg (exteriorPower.ιMulti ℂ 6)
  funext i
  change (ea (r • (v i).1), eb (s • (v i).2)) =
    (r • ea (v i).1, s • eb (v i).2)
  simp

theorem pull_mem (f : sector a' b') : pull ea eb f.val ∈ sector a b := by
  intro r s v
  have h := LinearMap.congr_fun (scaling_commutes ea eb r s) v
  change ((prodEquiv ea eb).exteriorPower 6) (((scaling a b r s).exteriorPower 6) v) =
    ((scaling a' b' r s).exteriorPower 6) (((prodEquiv ea eb).exteriorPower 6) v) at h
  change f.val _ = _ • f.val _
  simp only [IntertwiningMap.toLinearMap_apply, Representation.Equiv.coe_toIntertwiningMap]
  rw [h]
  exact f.property r s _

def pullLinear : sector a' b' →ₗ[ℂ] sector a b where
  toFun f := ⟨pull ea eb f.val, pull_mem ea eb f⟩
  map_add' f g := by apply Subtype.ext; ext v; rfl
  map_smul' z f := by apply Subtype.ext; ext v; rfl

theorem pull_symm (f : coefficients a b) :
    pull ea eb (pull ea.symm eb.symm f) = f := by
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  ext v
  change f (((prodEquiv ea.symm eb.symm).exteriorPower 6)
    (((prodEquiv ea eb).exteriorPower 6) (exteriorPower.ιMulti ℂ 6 v))) = _
  rw [Representation.Equiv.exteriorPower_apply_ιMulti,
    Representation.Equiv.exteriorPower_apply_ιMulti]
  change f _ = f (exteriorPower.ιMulti ℂ 6 v)
  apply congrArg f
  apply congrArg (exteriorPower.ιMulti ℂ 6)
  funext i
  change (ea.symm (ea (v i).1), eb.symm (eb (v i).2)) = v i
  simp

def degreeEquiv (ra : Representation ℂ H A) (rb : Representation ℂ H B) :
    sector ra rb ≃ₗ[ℂ] StatisticalCompleteness.sector
      (fun j : ℂ × ℂ => InvariantCoefficientTransport.pullbackMap
        ((scaling ra rb j.1 j.2).exteriorPower 6))
      (fun j => j.1 * j.1 * j.2 * j.2 * j.2 * j.2) where
  toFun f := ⟨f.val, by
    intro j
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    exact f.property j.1 j.2 v⟩
  invFun f := ⟨f.val, by
    intro r s v
    exact DFunLike.congr_fun (f.property (r, s)) v⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A concrete consumer of the same field-map constraint transport used for
statistics. Species degree is not an extra coefficient correspondence premise. -/
def equiv : sector a' b' ≃ₗ[ℂ] sector a b :=
  (degreeEquiv a' b').trans
    ((InvariantCoefficientTransport.alongConstraints
      ((prodEquiv ea eb).exteriorPower 6)
      (fun j : ℂ × ℂ => (scaling a b j.1 j.2).exteriorPower 6)
      (fun j : ℂ × ℂ => (scaling a' b' j.1 j.2).exteriorPower 6)
      (by intro j v; exact LinearMap.congr_fun (scaling_commutes ea eb j.1 j.2) v)
      (fun j => j.1 * j.1 * j.2 * j.2 * j.2 * j.2)).symm.trans
        (degreeEquiv a b).symm)

@[simp] theorem equiv_apply (f : sector a' b') :
    (equiv ea eb f).val = pull ea eb f.val := rfl

@[simp] theorem equiv_symm_apply (f : sector a b) :
    ((equiv ea eb).symm f).val = pull ea.symm eb.symm f.val := by
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  ext v
  rfl

include ea eb in
/-- Actual-field identifications neither create nor destroy nonzero coefficients. -/
theorem exists_nonzero_iff :
    (∃ f : sector a' b', f ≠ 0) ↔ ∃ f : sector a b, f ≠ 0 :=
  ConstrainedCompleteness.exists_nonzero_iff (equiv ea eb)

end
end Math.SixSlotSpeciesTransport
