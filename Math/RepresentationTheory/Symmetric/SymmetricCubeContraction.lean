import Math.LinearAlgebra.Symmetric.SymmetricCubeContraction
import Math.RepresentationTheory.Symmetric.SymmetricSquareContraction
import Math.RepresentationTheory.Symmetric.SymmetricCubeHook

/-! The cubic/dual contraction kernel is a full equivariant summand,
uniformly for finite-dimensional group actions. -/
namespace Math.SymmetricCubeContractionRepresentation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
open TensorSquareQuotients
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {G A : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  (r : Representation ℂ G A)
abbrev source := (r.symmetricPower 3).tprod r.dual
abbrev pair := r.tprod r.dual
@[reducible] local instance : AddCommGroup (SymmetricCubeContraction.Source (A := A)) := inferInstance
@[reducible] local instance : AddCommGroup (Sym[ℂ]^2 A) :=
  Module.addCommMonoidToAddCommGroup ℂ

def contract : IntertwiningMap (source r) (r.symmetricPower 2) where
  toLinearMap := SymmetricCubeContraction.contract
  isIntertwining' g := by
    apply SymmetricCubeContraction.source_ext
    intro a b c f
    change SymmetricCubeContraction.contract
        (SymmetricPower.map (ι := Fin 3) (r g) (SymmetricPower.tprod ℂ ![a,b,c]) ⊗ₜ[ℂ] r.dual g f)=
      r.symmetricPower 2 g
        (SymmetricCubeContraction.contract (SymmetricPower.tprod ℂ ![a,b,c] ⊗ₜ[ℂ] f))
    rw [← SymmetricCubeHook.symCube_natural,
      SymmetricCubeContraction.contract_pure, SymmetricCubeContraction.contract_pure]
    have he (x : A) : r.dual g f (r g x)=f x := by
      change f (r g⁻¹ (r g x))=f x
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [he, he, he, map_add, map_add, map_smul, map_smul, map_smul]
    simp only [Representation.symmetricPower_apply]
    rw [SymmetricCubeHook.sym_natural, SymmetricCubeHook.sym_natural,
      SymmetricCubeHook.sym_natural]

def insertPair : IntertwiningMap ((pair r).tprod (r.symmetricPower 2)) (source r) where
  toLinearMap := SymmetricCubeContraction.insertPair
  isIntertwining' g := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro f
    apply SymmetricPower.ext
    intro v
    rw [← sym_eta v]
    change SymmetricCubeContraction.insertPair
        ((r g a ⊗ₜ[ℂ] r.dual g f) ⊗ₜ[ℂ]
          SymmetricPower.map (ι := Fin 2) (r g) (sym (v 0 ⊗ₜ[ℂ] v 1)))=
      source r g (SymmetricCubeContraction.insertPair
        ((a ⊗ₜ[ℂ] f) ⊗ₜ[ℂ] sym (v 0 ⊗ₜ[ℂ] v 1)))
    rw [← SymmetricCubeHook.sym_natural, SymmetricCubeContraction.insertPair_pure,
      SymmetricCubeContraction.insertPair_pure, SymmetricCubeHook.symCube_natural]
    rfl

variable [FiniteDimensional ℂ A]

def sectionMap : IntertwiningMap (r.symmetricPower 2) (source r) where
  toLinearMap := SymmetricCubeContraction.sectionMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change ((Module.finrank ℂ A : ℂ)+2)⁻¹ •
        SymmetricCubeContraction.insertPair
          (SymmetricSquareContraction.coevaluation ⊗ₜ[ℂ] r.symmetricPower 2 g x)=
      source r g (((Module.finrank ℂ A : ℂ)+2)⁻¹ •
        SymmetricCubeContraction.insertPair (SymmetricSquareContraction.coevaluation ⊗ₜ[ℂ] x))
    rw [map_smul]
    apply congrArg (fun z => ((Module.finrank ℂ A : ℂ)+2)⁻¹ • z)
    have h := (insertPair r).isIntertwining _ _ g
      (SymmetricSquareContraction.coevaluation ⊗ₜ[ℂ] x)
    change SymmetricCubeContraction.insertPair
        (pair r g SymmetricSquareContraction.coevaluation ⊗ₜ[ℂ] r.symmetricPower 2 g x)=
      source r g (SymmetricCubeContraction.insertPair
        (SymmetricSquareContraction.coevaluation ⊗ₜ[ℂ] x)) at h
    rw [SymmetricSquareContractionRepresentation.coevaluation_fixed] at h
    exact h

abbrev kernel := (contract r).ker
abbrev action := (kernel r).toRepresentation

def remainder : IntertwiningMap (source r) (source r) :=
  IntertwiningMap.id _-(sectionMap r).comp (contract r)

def project : IntertwiningMap (source r) (action r) where
  toLinearMap := SymmetricCubeContraction.project
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (remainder r).isIntertwining _ _ g x

/-- The complete cubic/dual source splits into the symmetric square and
its actual contraction kernel, with the entire group action preserved. -/
def equivalence : Representation.Equiv (source r) ((r.symmetricPower 2).prod (action r)) where
  toLinearEquiv := SymmetricCubeContraction.equivalence
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact (contract r).isIntertwining _ _ g x
    · exact (project r).isIntertwining _ _ g x

end
end Math.SymmetricCubeContractionRepresentation
