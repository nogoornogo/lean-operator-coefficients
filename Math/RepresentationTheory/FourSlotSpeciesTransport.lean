import Math.RepresentationTheory.FourSlotRestrictionLift

/-! Species-preserving equivalences transport the independently defined degree sector. -/
namespace Math.FourSlotSpeciesTransport
set_option autoImplicit false
noncomputable section
open Representation FourSlotSpeciesDegree SplitRepresentationProjection

variable {H A B C A' B' C' : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
  [AddCommGroup A'] [Module ℂ A'] [AddCommGroup B'] [Module ℂ B'] [AddCommGroup C'] [Module ℂ C']
  {a : Representation ℂ H A} {b : Representation ℂ H B} {c : Representation ℂ H C}
  {a' : Representation ℂ H A'} {b' : Representation ℂ H B'} {c' : Representation ℂ H C'}
  (ea : Representation.Equiv a a') (eb : Representation.Equiv b b') (ec : Representation.Equiv c c')

def pull (f : coefficients a' b' c') : coefficients a b c :=
  f.comp ((prodEquiv ea (prodEquiv eb ec)).exteriorPower 4).toIntertwiningMap

theorem pull_mem (f : sector a' b' c') : pull ea eb ec f.val ∈ sector a b c := by
  obtain ⟨g, hg⟩ := FourSlotRestrictionLift.exists_ordered a' b' c' f.val f.property
  rw [pull, ← hg, ← FourSlotAlternation.coefficient_transport]
  exact coefficient_hasDegree a b c _

def pullLinear : sector a' b' c' →ₗ[ℂ] sector a b c where
  toFun f := ⟨pull ea eb ec f.val, pull_mem ea eb ec f⟩
  map_add' f g := by apply Subtype.ext; ext v; rfl
  map_smul' z f := by apply Subtype.ext; ext v; rfl

theorem pull_symm (f : coefficients a b c) :
    pull ea eb ec (pull ea.symm eb.symm ec.symm f) = f := by
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  ext v
  change f (((prodEquiv ea.symm (prodEquiv eb.symm ec.symm)).exteriorPower 4)
    (((prodEquiv ea (prodEquiv eb ec)).exteriorPower 4) (exteriorPower.ιMulti ℂ 4 v))) = _
  rw [Representation.Equiv.exteriorPower_apply_ιMulti, Representation.Equiv.exteriorPower_apply_ιMulti]
  change f _ = f (exteriorPower.ιMulti ℂ 4 v)
  apply congrArg f
  apply congrArg (exteriorPower.ιMulti ℂ 4)
  funext i
  change (ea.symm (ea (v i).1), eb.symm (eb (v i).2.1), ec.symm (ec (v i).2.2)) = v i
  simp

def equiv : sector a' b' c' ≃ₗ[ℂ] sector a b c where
  toFun := pullLinear ea eb ec
  invFun := pullLinear ea.symm eb.symm ec.symm
  left_inv f := by
    apply Subtype.ext
    exact pull_symm ea.symm eb.symm ec.symm f.val
  right_inv f := by apply Subtype.ext; exact pull_symm ea eb ec f.val
  map_add' := (pullLinear ea eb ec).map_add
  map_smul' := (pullLinear ea eb ec).map_smul

end
end Math.FourSlotSpeciesTransport
