import TauCeti.LinearAlgebra.ExteriorPower.Basis
import Math.RepresentationTheory.Symmetric.SymmetricCubeHook
import Math.RepresentationTheory.Exterior.ExteriorCubeDoublet

/-! The cubic hook of an actual SU2 doublet is the doublet itself.
This also resolves its mixed symmetric-square tensor by universal cubic maps. -/
namespace Math.DoubletCubicHook
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {G : Type*} [Group G] (j : G →* WeakDoubletScalars.Group)
abbrev B := WeakDoubletScalars.Doublet
abbrev spin := ExteriorCubeDoubletRepresentation.spin j
@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Source (V := B)) := inferInstance

theorem cube_zero (x : ⋀[ℂ]^3 B) : x=0 :=
  exteriorPower.eq_zero_of_finrank_lt 3 (by simp [B,WeakDoubletScalars.Doublet]) x

def hookFull : Representation.Equiv (ExteriorCubeHookRepresentation.action (spin j))
    (ExteriorCubeHookRepresentation.source (spin j)) where
  toLinearEquiv := LinearEquiv.ofBijective
    (ExteriorCubeHook.Hook (V := B)).subtype
    ⟨Subtype.val_injective,fun x => ⟨⟨x,cube_zero (ExteriorCubeHook.multiply x)⟩,rfl⟩⟩
  isIntertwining' := (ExteriorCubeHookRepresentation.hook (spin j)).subtype.isIntertwining'

def top2 : Representation.Equiv ((spin j).exteriorPower 2) (trivial ℂ G ℂ) where
  toLinearEquiv := Module.Basis.exteriorPowerTopEquiv (Pi.basisFun ℂ (Fin 2))
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change Module.Basis.exteriorPowerTopEquiv (Pi.basisFun ℂ (Fin 2))
      (exteriorPower.map 2 (spin j g) x)=_
    rw [Module.Basis.map_exteriorPower_top_eq_det_smul (Pi.basisFun ℂ (Fin 2)),
      ExteriorCubeDoubletRepresentation.spin_determinant j g,one_smul]
    rfl

def exteriorSource : Representation.Equiv
    (ExteriorCubeHookRepresentation.source (spin j)) (spin j) :=
  (tensorEquiv (.refl (spin j)) (top2 j)).trans (Representation.TensorProduct.rid ℂ (spin j))

def hookEquiv : Representation.Equiv (ExteriorCubeHookRepresentation.action (spin j)) (spin j) :=
  (hookFull j).trans (exteriorSource j)

def symmetricSource : Representation.Equiv (SymmetricCubeHookRepresentation.source (spin j))
    (((spin j).symmetricPower 3).prod (spin j)) :=
  (SymmetricCubeHookRepresentation.equivalence (spin j)).trans
    (SplitRepresentationProjection.prodEquiv (.refl _) (hookEquiv j))

end
end Math.DoubletCubicHook
