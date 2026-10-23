import Math.RepresentationTheory.Exterior.BinaryScalarExteriorSlice
import Math.RepresentationTheory.SU2.WeakDoubletScalars
import Math.RepresentationTheory.Constructions.CharacterTwistTransport
import Mathlib.LinearAlgebra.TensorProduct.Pi
import TauCeti.RepresentationTheory.ClassicalGroups.Diagonal

/-! The actual doublet tensor a retained representation, restricted to
its circle, is the sum of two oppositely twisted copies. -/
namespace Math.SU2DoubletTorusSplit
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor WeakDoubletScalars
open scoped TensorProduct
variable {K A : Type*} [Group K] [AddCommGroup A] [Module ℂ A]
  (s : Representation ℂ K A)
@[reducible] local instance : AddCommGroup (Doublet ⊗[ℂ] A) := inferInstance

abbrev weights := BinaryScalarExteriorSlice.weights
abbrev restrictionHom : Circle × K →* Group × K :=
  TauCeti.SU2.torusHom.prodMap (MonoidHom.id K)
abbrev source : Representation ℂ (Circle × K) (Doublet ⊗[ℂ] A) :=
  (external doublet s).comp (restrictionHom (K := K))

def fields (i : Fin 2) : Representation ℂ (Circle × K) A :=
  charTwist (((Circle.toUnits)^weights i).comp (MonoidHom.fst Circle K))
    (s.comp (MonoidHom.snd Circle K))

theorem fields_apply (i : Fin 2) (g : Circle × K) (x : A) :
    fields s i g x=(g.1 : ℂ)^(weights i) • s g.2 x := by
  simp [fields, Units.val_zpow_eq_zpow_val]

theorem fields_scalar (i : Fin 2) (z : Circle) (x : A) :
    fields s i (z,1) x=(z : ℂ)^(weights i) • x := by
  rw [fields_apply]
  simp

theorem doublet_torus (z : Circle) (v : Doublet) (i : Fin 2) :
    doublet (TauCeti.SU2.torusHom z) v i=(z : ℂ)^(weights i) * v i := by
  change TauCeti.stdRep ℂ 2 (TauCeti.SU2.toGL (TauCeti.SU2.torusHom z)) v i=_
  rw [TauCeti.SU2.toGL_torusHom, TauCeti.stdRep_diagGL_apply]
  fin_cases i <;> simp [weights, BinaryScalarExteriorSlice.weights]

def linearEquiv : Doublet ⊗[ℂ] A ≃ₗ[ℂ] (Fin 2 → A) :=
  (TensorProduct.comm ℂ Doublet A).trans (TensorProduct.piScalarRight ℂ ℂ A (Fin 2))

theorem linearEquiv_pure (v : Doublet) (x : A) (i : Fin 2) :
    linearEquiv (v ⊗ₜ[ℂ] x) i=v i • x := by
  simp [linearEquiv, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

def equivalence : Representation.Equiv (source s)
    (FiniteSpeciesExterior.representation (fields s)) where
  toLinearEquiv := linearEquiv
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v x
    funext i
    change linearEquiv ((doublet (TauCeti.SU2.torusHom g.1) v) ⊗ₜ[ℂ] s g.2 x) i=
      fields s i g (linearEquiv (v ⊗ₜ[ℂ] x) i)
    rw [linearEquiv_pure, linearEquiv_pure, fields_apply, doublet_torus, map_smul,
      smul_smul]

end
end Math.SU2DoubletTorusSplit
