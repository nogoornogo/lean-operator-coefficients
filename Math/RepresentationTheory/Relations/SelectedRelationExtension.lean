import Math.RepresentationTheory.Jets.DerivativeInterface

/-! Ordinary linear extension through the actual quotient image.
This does not assert an invariant extension outside the selected source. -/
namespace Math.SelectedRelationExtension
set_option autoImplicit false
noncomputable section
variable {H U : Type*} [Group H] [AddCommGroup U] [Module ℂ U]
  (P : DerivativeInterface.Input H U) (V : Submodule ℂ U)
  (hV : ∀ h, V ≤ V.comap (P.action h))

theorem exists_extension (F : (P.select V hV).Coefficient) :
    ∃ f : U →ₗ[ℂ] ℂ,
      (∀ p : V, f p.val = F.val p) ∧ P.relations ≤ f.ker := by
  let e := P.selectionEquiv V hV
  let qf : P.selectedImage V →ₗ[ℂ] ℂ :=
    ((P.select V hV).coefficientEquiv F).toLinearMap.comp e.symm.toLinearMap
  obtain ⟨g,hg⟩ := qf.exists_extend
  refine ⟨g.comp P.projection,?_,?_⟩
  · intro p
    have he := LinearMap.congr_fun hg (e ((P.select V hV).projection p))
    change g (e ((P.select V hV).projection p)).val =
      ((P.select V hV).coefficientEquiv F) (e.symm (e ((P.select V hV).projection p))) at he
    rw [e.symm_apply_apply] at he
    exact he
  · intro p hp
    change g (P.projection p) = 0
    have he : P.projection p = 0 := by
      apply (LinearMap.mem_ker).mp
      rw [DerivativeInterface.Input.projection,Submodule.ker_mkQ]
      exact hp
    rw [he,map_zero]

end
end Math.SelectedRelationExtension
