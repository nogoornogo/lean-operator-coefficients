import Math.LinearAlgebra.SymmetricSquarePartialTrace
import Math.RepresentationTheory.SymmetricSquareContraction
import Math.RepresentationTheory.SymmetricCubeHook

/-! Full equivariant partial-trace/kernel splitting of symmetric-square
times dual-square, with no irreducibility or multiplicity premise. -/
namespace Math.SymmetricSquarePartialTraceRepresentation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
open TensorSquareQuotients
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {G A : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  (r : Representation ℂ G A)
abbrev source := (r.symmetricPower 2).tprod (r.dual.symmetricPower 2)
abbrev pair := r.tprod r.dual
@[reducible] local instance : AddCommGroup (SymmetricSquarePartialTrace.Source (A := A)) := inferInstance

def contract : IntertwiningMap (source r) (pair r) where
  toLinearMap := SymmetricSquarePartialTrace.contract
  isIntertwining' g := by
    apply TensorProduct.ext
    apply SymmetricPower.ext
    intro v
    apply SymmetricPower.ext
    intro u
    rw [← sym_eta v, ← sym_eta u]
    change SymmetricSquarePartialTrace.contract
        (SymmetricPower.map (ι := Fin 2) (r g) (sym (v 0 ⊗ₜ[ℂ] v 1)) ⊗ₜ[ℂ]
          SymmetricPower.map (ι := Fin 2) (r.dual g) (sym (u 0 ⊗ₜ[ℂ] u 1)))=
      pair r g (SymmetricSquarePartialTrace.contract
        (sym (v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] sym (u 0 ⊗ₜ[ℂ] u 1)))
    rw [← SymmetricCubeHook.sym_natural, ← SymmetricCubeHook.sym_natural,
      SymmetricSquarePartialTrace.contract_pure, SymmetricSquarePartialTrace.contract_pure]
    have he (f : Module.Dual ℂ A) (x : A) : r.dual g f (r g x)=f x := by
      change f (r g⁻¹ (r g x))=f x
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [he, he, he, he]
    simp only [map_add, map_smul, Representation.tprod_apply, TensorProduct.map_tmul]

def insertPair : IntertwiningMap ((pair r).tprod (pair r)) (source r) where
  toLinearMap := SymmetricSquarePartialTrace.insertPair
  isIntertwining' g := by
    ext a f b h
    change sym (r g a ⊗ₜ[ℂ] r g b) ⊗ₜ[ℂ] sym (r.dual g f ⊗ₜ[ℂ] r.dual g h)=
      SymmetricPower.map (ι := Fin 2) (r g) (sym (a ⊗ₜ[ℂ] b)) ⊗ₜ[ℂ]
        SymmetricPower.map (ι := Fin 2) (r.dual g) (sym (f ⊗ₜ[ℂ] h))
    rw [SymmetricCubeHook.sym_natural, SymmetricCubeHook.sym_natural]

variable [FiniteDimensional ℂ A]

def insert : IntertwiningMap (pair r) (source r) where
  toLinearMap := SymmetricSquarePartialTrace.insert
  isIntertwining' g := by
    apply LinearMap.ext
    intro p
    have h := (insertPair r).isIntertwining _ _ g
      (p ⊗ₜ[ℂ] SymmetricSquareContraction.coevaluation)
    change SymmetricSquarePartialTrace.insertPair
        (pair r g p ⊗ₜ[ℂ] pair r g SymmetricSquareContraction.coevaluation)=
      source r g (SymmetricSquarePartialTrace.insert p) at h
    rw [SymmetricSquareContractionRepresentation.coevaluation_fixed] at h
    exact h

def trace : IntertwiningMap (pair r) (trivial ℂ G ℂ) :=
  (TraceEndomorphismSplit.trace r).comp (SymmetricSquareContractionRepresentation.pairEnd r).toIntertwiningMap

def scalar : IntertwiningMap (trivial ℂ G ℂ) (pair r) :=
  (SymmetricSquareContractionRepresentation.pairEnd r).symm.toIntertwiningMap.comp
    (TraceEndomorphismSplit.scalar r)

def correct : IntertwiningMap (pair r) (pair r) :=
  ((Module.finrank ℂ A : ℂ)+2)⁻¹ •
    (IntertwiningMap.id _-((2 : ℂ)*(Module.finrank ℂ A : ℂ)+2)⁻¹ •
      (scalar r).comp (trace r))

theorem correct_apply (p : SymmetricSquarePartialTrace.Pair (A := A)) :
    correct r p=SymmetricSquarePartialTrace.correct p := by
  change ((Module.finrank ℂ A : ℂ)+2)⁻¹ •
    (p-((2 : ℂ)*(Module.finrank ℂ A : ℂ)+2)⁻¹ •
      SymmetricSquareContraction.pairEnd.symm
        (LinearMap.trace ℂ A (SymmetricSquareContraction.pairEnd p) • LinearMap.id))=_
  rw [map_smul]
  rfl

def sectionMap : IntertwiningMap (pair r) (source r) := (insert r).comp (correct r)

theorem sectionMap_apply (p : SymmetricSquarePartialTrace.Pair (A := A)) :
    sectionMap r p=SymmetricSquarePartialTrace.sectionMap p := by
  change SymmetricSquarePartialTrace.insert (correct r p)=_
  rw [correct_apply]
  rfl

abbrev kernel := (contract r).ker
abbrev action := (kernel r).toRepresentation

def remainder : IntertwiningMap (source r) (source r) :=
  IntertwiningMap.id _-(sectionMap r).comp (contract r)

def project : IntertwiningMap (source r) (action r) where
  toLinearMap := SymmetricSquarePartialTrace.project
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := (remainder r).isIntertwining _ _ g x
    change source r g x-sectionMap r (contract r (source r g x))=
      source r g (x-sectionMap r (contract r x)) at h
    simp only [sectionMap_apply] at h
    exact h

def equivalence : Representation.Equiv (source r) ((pair r).prod (action r)) where
  toLinearEquiv := SymmetricSquarePartialTrace.equivalence
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact (contract r).isIntertwining _ _ g x
    · exact (project r).isIntertwining _ _ g x

end
end Math.SymmetricSquarePartialTraceRepresentation
