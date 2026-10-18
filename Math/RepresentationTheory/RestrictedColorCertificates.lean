import Math.RepresentationTheory.RestrictedColorVertices
import Math.RepresentationTheory.TraceFreeColorVertex
import Math.RepresentationTheory.SymmetricVertexCertificate

/-! The actual reachable color kernels satisfy the symmetry and trace
conditions needed for exclusion of invalid contraction diagrams. -/
namespace Math.RestrictedColorCertificates
set_option autoImplicit false
noncomputable section
open Representation SymmetricVertexCertificate
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (rho : Representation ℂ G V)

@[reducible] local instance : AddCommGroup
    (SymmetricSquareContractionRepresentation.kernel rho).toSubmodule :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup
    (SymmetricCubeContractionRepresentation.kernel rho).toSubmodule :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup
    (SymmetricSquarePartialTraceRepresentation.kernel rho).toSubmodule :=
  Module.addCommMonoidToAddCommGroup ℂ

theorem square_symmetric : Symmetric rho (RestrictedColorVertices.square rho) := by
  intro x
  exact ⟨RestrictedColorTraces.addDualOne 2 x.val,(RestrictedColorVertices.square_embed rho x).symm⟩

theorem cube_symmetric : Symmetric rho (RestrictedColorVertices.cube rho) := by
  intro x
  exact ⟨RestrictedColorTraces.addDualOne 3 x.val,(RestrictedColorVertices.cube_embed rho x).symm⟩

theorem squareSquare_symmetric : Symmetric rho (RestrictedColorVertices.squareSquare rho) := by
  intro x
  exact ⟨x.val,(RestrictedColorVertices.squareSquare_embed rho x).symm⟩

theorem square_traceless : Traceless rho (RestrictedColorVertices.square rho) := by
  intro c d hp hq x
  have hc : c=1 := by omega
  have hd : d=0 := by omega
  subst c
  subst d
  rw [cast_refl]
  exact RestrictedColorVertices.square_trace_zero rho x

theorem cube_traceless : Traceless rho (RestrictedColorVertices.cube rho) := by
  intro c d hp hq x
  have hc : c=2 := by omega
  have hd : d=0 := by omega
  subst c
  subst d
  rw [cast_refl]
  exact RestrictedColorVertices.cube_trace_zero rho x

theorem squareSquare_traceless : Traceless rho (RestrictedColorVertices.squareSquare rho) := by
  intro c d hp hq x
  have hc : c=1 := by omega
  have hd : d=1 := by omega
  subst c
  subst d
  rw [cast_refl]
  exact RestrictedColorVertices.squareSquare_trace_zero rho x

omit [FiniteDimensional ℂ V] in
theorem inclusion_projection_one (z : SymmetricTensorTrace.Raw (V := V) 1 1) :
    SymmetricTensorTrace.inclusion rho 1 1 (SymmetricTensorTrace.projection rho 1 1 z) = z := by
  have he : (SymmetricTensorTrace.inclusion rho 1 1).comp
      (SymmetricTensorTrace.projection rho 1 1) = LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    obtain ⟨v,rfl⟩ := (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) 0).symm.surjective x
    obtain ⟨f,rfl⟩ := (PiTensorProduct.subsingletonEquiv (R := ℂ)
      (s := fun _ : Fin 1 => Module.Dual ℂ V) 0).symm.surjective y
    rw [PiTensorProduct.subsingletonEquiv_symm_apply',PiTensorProduct.subsingletonEquiv_symm_apply']
    change SymmetricTensorTrace.inclusion rho 1 1
      (SymmetricPower.tprod ℂ (fun _ : Fin 1 => v) ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ (fun _ : Fin 1 => f)) = _
    exact RestrictedColorVertices.symmetric_pure rho 1 1 v f
  exact LinearMap.congr_fun he z

theorem adjoint_symmetric (hd : Module.finrank ℂ V ≠ 0) :
    Symmetric rho (TraceFreeColorVertex.split rho hd) := by
  intro x
  exact ⟨SymmetricTensorTrace.projection rho 1 1 ((TraceFreeColorVertex.split rho hd).embed x),
    inclusion_projection_one rho _⟩

theorem adjoint_traceless (hd : Module.finrank ℂ V ≠ 0) :
    Traceless rho (TraceFreeColorVertex.split rho hd) := by
  intro c d hp hq x
  have hc : c=0 := by omega
  have hd' : d=0 := by omega
  subst c
  subst d
  rw [cast_refl]
  exact TraceFreeColorVertex.trace_zero rho hd x

end
end Math.RestrictedColorCertificates
