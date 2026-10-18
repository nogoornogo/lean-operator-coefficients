import Math.RepresentationTheory.Characters.CompactHomDimension

/-! Joint continuity of the algebraic contragredient in finite dimension.
The norm below is local auxiliary data, not a replacement for the algebraic dual. -/

namespace Math.ContinuousDual
noncomputable section

open ContinuousRepresentationScope

variable {H V : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

@[instance_reducible]
def dualNormedAddCommGroup : NormedAddCommGroup (Module.Dual ℂ V) :=
  NormedAddCommGroup.induced _ _
    (LinearMap.toContinuousLinearMap : Module.Dual ℂ V ≃ₗ[ℂ] (V →L[ℂ] ℂ)).toAddEquiv.toAddMonoidHom
    LinearMap.toContinuousLinearMap.injective

@[instance_reducible]
def dualNormedSpace : letI := dualNormedAddCommGroup (V := V)
    NormedSpace ℂ (Module.Dual ℂ V) := by
  letI := dualNormedAddCommGroup (V := V)
  exact NormedSpace.induced ℂ _ _
    (LinearMap.toContinuousLinearMap : Module.Dual ℂ V ≃ₗ[ℂ] (V →L[ℂ] ℂ)).toLinearMap

/-- The algebraic dual, equipped with its induced operator norm, has a
jointly continuous contragredient action. -/
theorem jointlyContinuous_dual
    (rho : Representation ℂ H V) (hr : IsJointlyContinuous rho) :
    letI := dualNormedAddCommGroup (V := V)
    letI := dualNormedSpace (V := V)
    IsJointlyContinuous rho.dual := by
  let := dualNormedAddCommGroup (V := V)
  let := dualNormedSpace (V := V)
  let e := (LinearMap.toContinuousLinearMap :
    Module.Dual ℂ V ≃ₗ[ℂ] (V →L[ℂ] ℂ)).toContinuousLinearEquiv
  change Continuous (fun p : H × Module.Dual ℂ V => rho.dual p.1 p.2)
  rw [← e.comp_continuous_iff]
  apply continuous_clm_apply.mpr
  intro v
  exact (e.continuous.comp continuous_snd).clm_apply
    ((hr.orbit v).comp (continuous_inv.comp continuous_fst))

end
end Math.ContinuousDual
