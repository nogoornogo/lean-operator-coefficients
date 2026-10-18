import Physics.StandardModel.Operators.SixQuarkFlavorResidualHom

/-! The scalar-flavor specialization recovers the two-probe classification.
This is a specialization, not a dimension formula for arbitrary multiplicities. -/
namespace GUT.SixQuarkFlavorOneGeneration
set_option autoImplicit false
noncomputable section
open SixQuarkInvariant SixQuarkSpeciesQuotient SixQuarkFlavorCoordinates
open SixQuarkFlavorResidualHom
open scoped TensorProduct

abbrev scalarAction : Fin 6 → Representation ℂ Unit ℂ :=
  fun _ => Representation.trivial ℂ Unit ℂ

private theorem rid_map (a : Quark →ₗ[ℂ] Quark) (v : Quark ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ Quark (TensorProduct.map a LinearMap.id v) =
      a (TensorProduct.rid ℂ Quark v) := by
  have he : (TensorProduct.rid ℂ Quark).toLinearMap.comp
      (TensorProduct.map a LinearMap.id) =
      a.comp (TensorProduct.rid ℂ Quark).toLinearMap := by
    apply TensorProduct.ext
    ext q z
    simp
  exact DFunLike.congr_fun he v

def forgetFlavor (f : Coefficients scalarAction) : admissible := by
  refine ⟨fixedFlavor f.val (fun _ => 1), fixedFlavor_invariant _ f.property.1 _, ?_⟩
  intro p hp q
  simpa [fixedFlavor_apply, Function.comp_def] using
    f.property.2.2 p hp (fun i => q i ⊗ₜ[ℂ] (1 : ℂ))

def addFlavor (f : admissible) : Coefficients scalarAction := by
  refine ⟨f.val.compLinearMap (fun _ => (TensorProduct.rid ℂ Quark).toLinearMap),
    ⟨?_, ?_⟩, ?_, ?_⟩
  · intro g v
    change f.val (fun i => TensorProduct.rid ℂ Quark
      (TensorProduct.map (colorAction g) LinearMap.id (v i))) =
        f.val (fun i => TensorProduct.rid ℂ Quark (v i))
    simp_rw [rid_map]
    exact f.property.1.1 g _
  · intro g v
    change f.val (fun i => TensorProduct.rid ℂ Quark
      (TensorProduct.map (spinAction g) LinearMap.id (v i))) =
        f.val (fun i => TensorProduct.rid ℂ Quark (v i))
    simp_rw [rid_map]
    exact f.property.1.2 g _
  · intro g v
    change f.val (fun i => TensorProduct.rid ℂ Quark
      (TensorProduct.map LinearMap.id LinearMap.id (v i))) = _
    simp
  · intro p hp v
    exact f.property.2 p hp (fun i => TensorProduct.rid ℂ Quark (v i))

def scalarFlavorEquiv : Coefficients scalarAction ≃ₗ[ℂ] admissible where
  toFun := forgetFlavor
  invFun := addFlavor
  left_inv f := by
    apply Subtype.ext
    apply SixQuarkFlavorCoordinates.pure_ext
    intro q t
    change fixedFlavor f.val (fun _ => 1)
      (fun i => TensorProduct.rid ℂ Quark (q i ⊗ₜ[ℂ] t i)) =
        f.val (fun i => q i ⊗ₜ[ℂ] t i)
    simp only [TensorProduct.rid_tmul, fixedFlavor_apply]
    simp [TensorProduct.smul_tmul, smul_eq_mul]
  right_inv f := by
    apply Subtype.ext
    ext q
    change f.val (fun i => TensorProduct.rid ℂ Quark (q i ⊗ₜ[ℂ] (1 : ℂ))) = f.val q
    simp
  map_add' f g := by apply Subtype.ext; ext q; rfl
  map_smul' z f := by apply Subtype.ext; ext q; rfl

/-- Exact recovery of the established two-probe inverse at scalar flavors. -/
def twoProbeEquiv : Coefficients scalarAction ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  scalarFlavorEquiv.trans coefficientProbeEquiv

def homTwoProbeEquiv : StatisticsHom scalarAction ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  (statisticsLinearEquiv scalarAction).symm.trans twoProbeEquiv

theorem finrank_scalarFlavor : Module.finrank ℂ (Coefficients scalarAction) = 2 := by
  rw [twoProbeEquiv.finrank_eq]
  simp

theorem finrank_scalarHom : Module.finrank ℂ (StatisticsHom scalarAction) = 2 := by
  rw [homTwoProbeEquiv.finrank_eq]
  simp

end
end GUT.SixQuarkFlavorOneGeneration
