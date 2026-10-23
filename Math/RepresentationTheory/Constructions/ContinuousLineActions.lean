import Math.RepresentationTheory.SU2.SU2FiniteBranching
import Math.LinearAlgebra.Symmetric.SymmetricPowerLowDegree
import Math.LieGroups.SpecialUnitary.ColorPlaneCircles

/-! Continuous one-dimensional actions of the semisimple compact factors
are trivial. This is a structural line theorem, not a numerical certificate. -/
namespace Math.ContinuousLineActions
set_option autoImplicit false
noncomputable section
open Representation ContinuousRepresentationScope SU2FiniteBranching

theorem transport_id {G A B : Type*} [Group G]
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    {rho : Representation ℂ G A} {sigma : Representation ℂ G B}
    (e : Representation.Equiv rho sigma) (g : G) (h : rho g=LinearMap.id) :
    sigma g=LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := e.surjective x
  have he := e.toIntertwiningMap.isIntertwining _ _ g y
  rw [h] at he
  exact he.symm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem su2 (rho : Representation ℂ TauCeti.SU2 V) (hr : IsJointlyContinuous rho)
    (hd : Module.finrank ℂ V=1) (g : TauCeti.SU2) : rho g=LinearMap.id := by
  let C := (exists_certificate_of_dimension rho hr).some
  apply C.decomposition.action_eq_id_of_forall_block g
  intro i
  have hdeg : (C.degree i).val=0 := by
    have hb := C.decomposition.block_finrank_le i
    rw [← (C.blockEquiv i).finrank_eq,TauCeti.SU2.finrank_symPower] at hb
    omega
  let e : Representation.Equiv (C.decomposition.subrepresentation i).toRepresentation
      (Representation.trivial ℂ TauCeti.SU2 ℂ) :=
    (C.decomposition.blockAmbientEquiv i).symm.trans
      ((C.blockEquiv i).symm.trans (by
        rw [hdeg]
        exact SymmetricPowerLowDegree.representationZeroEquiv WeakDoubletScalars.doublet))
  apply LinearMap.ext
  intro x
  apply e.injective
  exact e.toIntertwiningMap.isIntertwining _ _ g x

theorem color_embedding_continuous (i : Fin 3) : Continuous (ColorPlaneCircles.embedding i) := by
  change Continuous (fun u : ColorPlaneCircles.SU2 =>
    ColorPlaneCircles.frame i * SUN.Block.inclusion 2 1 u * (ColorPlaneCircles.frame i)⁻¹)
  exact (continuous_const.mul (SUN.Block.inclusion_continuous 2 1)).mul continuous_const

theorem su3 (rho : Representation ℂ SU3PlaneGeneration.SU3 V) (hr : IsJointlyContinuous rho)
    (hd : Module.finrank ℂ V=1) (g : SU3PlaneGeneration.SU3) : rho g=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply (Module.finBasis ℂ V).repr.injective
  ext i
  exact ColorPlaneCircles.invariant rho ((Module.finBasis ℂ V).coord i)
    (by
      intro j u y
      have he := su2 (rho.comp (ColorPlaneCircles.embedding j))
        (hr.comp (⟨ColorPlaneCircles.embedding j,color_embedding_continuous j⟩ : _ →ₜ* _)) hd u
      exact congrArg ((Module.finBasis ℂ V).coord i) (DFunLike.congr_fun he y)) g x

end
end Math.ContinuousLineActions
