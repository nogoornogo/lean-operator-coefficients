import Math.RepresentationTheory.ColorFlagVertex
import Math.RepresentationTheory.RestrictedColorCertificates

/-! All concrete reachable flag vertices satisfy the local symmetry and
trace exclusions, including opposite and actual dual actions. -/
namespace Math.ColorVertexCertificates
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior SymmetricVertexCertificate
open scoped TensorProduct

structure Certified (v : ColorFlagVertex.Vertex) : Prop where
  symmetric : Symmetric rho v.split
  traceless : Traceless rho v.split

theorem alongEquiv {A : Type} [AddCommGroup A] [Module ℂ A]
    (v : ColorFlagVertex.Vertex) (a : Representation ℂ Group A)
    (e : Representation.Equiv v.action a) (h : Certified v) :
    Certified (ColorFlagVertex.alongEquiv v a e) :=
  ⟨symmetric_transport rho v.split e h.symmetric,
    traceless_transport rho v.split e h.traceless⟩

theorem square : Certified ColorFlagVertex.square :=
  ⟨RestrictedColorCertificates.square_symmetric rho,RestrictedColorCertificates.square_traceless rho⟩
theorem cube : Certified ColorFlagVertex.cube :=
  ⟨RestrictedColorCertificates.cube_symmetric rho,RestrictedColorCertificates.cube_traceless rho⟩
theorem squareSquare : Certified ColorFlagVertex.squareSquare :=
  ⟨RestrictedColorCertificates.squareSquare_symmetric rho,RestrictedColorCertificates.squareSquare_traceless rho⟩
theorem adjoint : Certified ColorFlagVertex.adjoint :=
  ⟨RestrictedColorCertificates.adjoint_symmetric rho ColorFlagVertex.dimension_ne_zero,
    RestrictedColorCertificates.adjoint_traceless rho ColorFlagVertex.dimension_ne_zero⟩

@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (Sym[ℂ]^n A) := Module.addCommMonoidToAddCommGroup ℂ

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance
@[reducible] local instance : AddCommGroup
    (SymmetricSquareContractionRepresentation.kernel rho.dual).toSubmodule :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup
    (SymmetricCubeContractionRepresentation.kernel rho.dual).toSubmodule :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup
    (SymmetricSquarePartialTraceRepresentation.kernel rho.dual).toSubmodule :=
  Module.addCommMonoidToAddCommGroup ℂ

theorem positiveSymmetric (n : ℕ) : Certified (ColorFlagVertex.positiveSymmetric n) := by
  constructor
  · intro x
    let u := SymmetricPower.tprod ℂ (fun _ : Fin 0 => (0 : Module.Dual ℂ Vector))
    let L := (TensorProduct.mk ℂ (Sym[ℂ]^n Vector) (Sym[ℂ]^0 (Module.Dual ℂ Vector))).flip u
    have he : (SymmetricTensorTrace.inclusion rho n 0).comp L =
        (ColorFlagVertex.positiveSymmetricSplit n).embed.toLinearMap := by
      apply SymmetricPurePowers.ext (V := Vector)
      intro v
      change SymmetricTensorTrace.inclusion rho n 0
        (SymmetricPower.tprod ℂ (fun _ : Fin n => v) ⊗ₜ[ℂ] u) = _
      exact (RestrictedColorVertices.symmetric_pure rho n 0 v 0).trans
        (ColorFlagVertex.positiveSymmetric_flag n v 0).symm
    exact ⟨L x,LinearMap.congr_fun he x⟩
  · intro c d hp hq
    change 0=1+d at hq
    omega

theorem negativeSymmetric (n : ℕ) : Certified (ColorFlagVertex.negativeSymmetric n) := by
  constructor
  · intro x
    let u := SymmetricPower.tprod ℂ (fun _ : Fin 0 => (0 : Vector))
    let L := TensorProduct.mk ℂ (Sym[ℂ]^0 Vector) (Sym[ℂ]^n (Module.Dual ℂ Vector)) u
    have he : (SymmetricTensorTrace.inclusion rho 0 n).comp L =
        (ColorFlagVertex.negativeSymmetricSplit n).embed.toLinearMap := by
      apply SymmetricPurePowers.ext (V := Module.Dual ℂ Vector)
      intro f
      change SymmetricTensorTrace.inclusion rho 0 n
        (u ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun _ : Fin n => f)) = _
      exact (RestrictedColorVertices.symmetric_pure rho 0 n 0 f).trans
        (ColorFlagVertex.negativeSymmetric_flag n 0 f).symm
    exact ⟨L x,LinearMap.congr_fun he x⟩
  · intro c d hp hq
    change 0=1+c at hp
    omega

theorem ofDual {A : Type} [AddCommGroup A] [Module ℂ A]
    (p q : ℕ) (r : Representation ℂ Group A)
    (S : SplitRepresentationProjection.Split
      ((rho.dual.tensorPower p).tprod (rho.dual.dual.tensorPower q)) r)
    (flagD : ∀ (f : Module.Dual ℂ Vector) (v : Module.Dual ℂ (Module.Dual ℂ Vector)), v f=0 → A)
    (he : ∀ f v (hf : v f=0), S.embed (flagD f v hf) =
      PiTensorProduct.tprod ℂ (fun _ : Fin p => f) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin q => v))
    (hs : Symmetric rho.dual S) (ht : Traceless rho.dual S) :
    Certified (ColorFlagVertex.ofDual p q r S flagD he) :=
  ⟨symmetric_swapped rho S hs,traceless_swapped rho S hs ht⟩

theorem oppositeSquare : Certified ColorFlagVertex.oppositeSquare := by
  apply ofDual
  · exact RestrictedColorCertificates.square_symmetric rho.dual
  · exact RestrictedColorCertificates.square_traceless rho.dual

theorem oppositeCube : Certified ColorFlagVertex.oppositeCube := by
  apply ofDual
  · exact RestrictedColorCertificates.cube_symmetric rho.dual
  · exact RestrictedColorCertificates.cube_traceless rho.dual

theorem oppositeSquareSquare : Certified ColorFlagVertex.oppositeSquareSquare := by
  apply ofDual
  · exact RestrictedColorCertificates.squareSquare_symmetric rho.dual
  · exact RestrictedColorCertificates.squareSquare_traceless rho.dual

theorem oppositeAdjoint : Certified ColorFlagVertex.oppositeAdjoint := by
  apply ofDual
  · exact RestrictedColorCertificates.adjoint_symmetric rho.dual ColorFlagVertex.dual_dimension_ne_zero
  · exact RestrictedColorCertificates.adjoint_traceless rho.dual ColorFlagVertex.dual_dimension_ne_zero

theorem squareDual : Certified ColorFlagVertex.squareDual :=
  alongEquiv _ _ _ oppositeSquare
theorem cubeDual : Certified ColorFlagVertex.cubeDual :=
  alongEquiv _ _ _ oppositeCube
theorem squareSquareDual : Certified ColorFlagVertex.squareSquareDual :=
  alongEquiv _ _ _ oppositeSquareSquare
theorem adjointDual : Certified ColorFlagVertex.adjointDual :=
  alongEquiv _ _ _ oppositeAdjoint
theorem symmetricDual (n : ℕ) : Certified (ColorFlagVertex.symmetricDual n) :=
  alongEquiv _ _ _ (negativeSymmetric n)
theorem oppositeSymmetricDual (n : ℕ) : Certified (ColorFlagVertex.oppositeSymmetricDual n) :=
  alongEquiv _ _ _ (positiveSymmetric n)
theorem oppositeSquareDual : Certified ColorFlagVertex.oppositeSquareDual :=
  alongEquiv _ _ _ square
theorem oppositeCubeDual : Certified ColorFlagVertex.oppositeCubeDual :=
  alongEquiv _ _ _ cube
theorem oppositeSquareSquareDual : Certified ColorFlagVertex.oppositeSquareSquareDual :=
  alongEquiv _ _ _ squareSquare
theorem oppositeAdjointDual : Certified ColorFlagVertex.oppositeAdjointDual :=
  alongEquiv _ _ _ adjoint

end
end Math.ColorVertexCertificates
