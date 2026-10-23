import Math.LinearAlgebra.Symmetric.SymmetricSquareContraction
import Math.RepresentationTheory.Constructions.TraceEndomorphismSplit
import Math.RepresentationTheory.Exterior.SymmetricSquareCauchy

/-! The actual trace-free symmetric-square/dual summand, with its full
group action and a canonical equivariant complement. -/
namespace Math.SymmetricSquareContractionRepresentation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
open TensorSquareQuotients
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {G A : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  (r : Representation ℂ G A)
abbrev source := (r.symmetricPower 2).tprod r.dual
abbrev pair := r.tprod r.dual
@[reducible] local instance : AddCommGroup (SymmetricSquareContraction.Source (A := A)) := inferInstance

def contract : IntertwiningMap (source r) r where
  toLinearMap := SymmetricSquareContraction.contract
  isIntertwining' g := by
    apply TensorProduct.ext
    apply SymmetricPower.ext
    intro v
    apply LinearMap.ext
    intro f
    rw [← sym_eta v]
    change SymmetricSquareContraction.contract
        (SymmetricPower.map (ι := Fin 2) (r g) (sym (v 0 ⊗ₜ[ℂ] v 1)) ⊗ₜ[ℂ] r.dual g f)=
      r g (SymmetricSquareContraction.contract (sym (v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] f))
    rw [← SymmetricSquareCauchyRepresentation.sym_natural,
      SymmetricSquareContraction.contract_pure, SymmetricSquareContraction.contract_pure]
    have he (a : A) : r.dual g f (r g a)=f a := by
      change f (r g⁻¹ (r g a))=f a
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [he, he, map_add, map_smul, map_smul]

def insertPair : IntertwiningMap ((pair r).tprod r) (source r) where
  toLinearMap := SymmetricSquareContraction.insertPair
  isIntertwining' g := by
    ext a f b
    change sym (r g a ⊗ₜ[ℂ] r g b) ⊗ₜ[ℂ] r.dual g f=
      SymmetricPower.map (ι := Fin 2) (r g) (sym (a ⊗ₜ[ℂ] b)) ⊗ₜ[ℂ] r.dual g f
    rw [SymmetricSquareCauchyRepresentation.sym_natural]

variable [FiniteDimensional ℂ A]

def pairEnd : Representation.Equiv (pair r) (TraceEndomorphismSplit.action r) :=
  (Representation.TensorProduct.comm r r.dual).trans (Representation.Equiv.dualTensorHom r r)

theorem coevaluation_fixed (g : G) :
    pair r g (SymmetricSquareContraction.coevaluation (A := A))=
      SymmetricSquareContraction.coevaluation := by
  apply (pairEnd r).injective
  have h := LinearMap.congr_fun ((pairEnd r).isIntertwining' g)
    (SymmetricSquareContraction.coevaluation (A := A))
  change SymmetricSquareContraction.pairEnd
      (pair r g SymmetricSquareContraction.coevaluation)=
    TraceEndomorphismSplit.action r g
      (SymmetricSquareContraction.pairEnd (SymmetricSquareContraction.pairEnd.symm LinearMap.id)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  change SymmetricSquareContraction.pairEnd
      (pair r g SymmetricSquareContraction.coevaluation)=
    SymmetricSquareContraction.pairEnd (SymmetricSquareContraction.pairEnd.symm LinearMap.id)
  rw [LinearEquiv.apply_symm_apply, h]
  ext a
  change r g (r g⁻¹ a)=a
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

def sectionMap : IntertwiningMap r (source r) where
  toLinearMap := SymmetricSquareContraction.sectionMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro a
    change ((Module.finrank ℂ A : ℂ)+1)⁻¹ •
        SymmetricSquareContraction.insertPair (SymmetricSquareContraction.coevaluation ⊗ₜ[ℂ] r g a)=
      source r g (((Module.finrank ℂ A : ℂ)+1)⁻¹ •
        SymmetricSquareContraction.insertPair (SymmetricSquareContraction.coevaluation ⊗ₜ[ℂ] a))
    rw [map_smul]
    apply congrArg (fun z => ((Module.finrank ℂ A : ℂ)+1)⁻¹ • z)
    have h := (insertPair r).isIntertwining _ _ g
      (SymmetricSquareContraction.coevaluation ⊗ₜ[ℂ] a)
    change SymmetricSquareContraction.insertPair
      (pair r g SymmetricSquareContraction.coevaluation ⊗ₜ[ℂ] r g a)=
      source r g (SymmetricSquareContraction.insertPair
        (SymmetricSquareContraction.coevaluation ⊗ₜ[ℂ] a)) at h
    rw [coevaluation_fixed] at h
    exact h

abbrev kernel := (contract r).ker
abbrev action := (kernel r).toRepresentation

def remainder : IntertwiningMap (source r) (source r) :=
  IntertwiningMap.id _-(sectionMap r).comp (contract r)

def project : IntertwiningMap (source r) (action r) where
  toLinearMap := SymmetricSquareContraction.project
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (remainder r).isIntertwining _ _ g x

/-- Full contraction/kernel split, for any finite-dimensional group action. -/
def equivalence : Representation.Equiv (source r) (r.prod (action r)) where
  toLinearEquiv := SymmetricSquareContraction.equivalence
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact (contract r).isIntertwining _ _ g x
    · exact (project r).isIntertwining _ _ g x

end
end Math.SymmetricSquareContractionRepresentation
