import Math.RepresentationTheory.Exterior.SymmetricSquareCauchy
import Math.RepresentationTheory.Tensors.InvariantTensorCurry
import TauCeti.LinearAlgebra.SymmetricPower.Basis

/-! Perfect symmetric-square duality in arbitrary finite dimension. This
does not require irreducibility of the symmetric square. -/
namespace Math.SymmetricSquareDual
set_option autoImplicit false
noncomputable section
open Representation TensorSquareQuotients
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]

def tensorPairing : ((Module.Dual ℂ A) ⊗[ℂ] Module.Dual ℂ A) ≃ₗ[ℂ]
    Module.Dual ℂ (A ⊗[ℂ] A) := TensorProduct.dualDistribEquiv ℂ A A

theorem tensorPairing_pure (f g : Module.Dual ℂ A) (a b : A) :
    tensorPairing (f ⊗ₜ[ℂ] g) (a ⊗ₜ[ℂ] b)=g b*f a := rfl

def raw : ((Module.Dual ℂ A) ⊗[ℂ] Module.Dual ℂ A) →ₗ[ℂ] Module.Dual ℂ (Sym[ℂ]^2 A) :=
  (symmetricSection (A := A)).dualMap.comp tensorPairing.toLinearMap

theorem raw_pure (f g : Module.Dual ℂ A) (a b : A) :
    raw (f ⊗ₜ[ℂ] g) (sym (a ⊗ₜ[ℂ] b))=f a*g b+f b*g a := by
  change tensorPairing (f ⊗ₜ[ℂ] g) (symmetricSection (sym (a ⊗ₜ[ℂ] b)))=_
  rw [symmetricSection_pure, map_add]
  simp only [tensorPairing, TensorProduct.dualDistribEquiv_tmul_tmul]
  ring

theorem raw_symmetric (f g : Module.Dual ℂ A) : raw (g ⊗ₜ[ℂ] f)=raw (f ⊗ₜ[ℂ] g) := by
  apply SymmetricPower.ext
  intro v
  rw [← sym_eta v, raw_pure, raw_pure]
  ring

def pairing : Sym[ℂ]^2 (Module.Dual ℂ A) →ₗ[ℂ] Module.Dual ℂ (Sym[ℂ]^2 A) :=
  symmetricLift raw raw_symmetric

theorem pairing_pure (f g : Module.Dual ℂ A) (a b : A) :
    pairing (sym (f ⊗ₜ[ℂ] g)) (sym (a ⊗ₜ[ℂ] b))=f a*g b+f b*g a := by
  rw [pairing, symmetricLift_pure, raw_pure]

theorem tensor_identity : (tensorPairing (A := A)).toLinearMap.comp symmetricSection=
    (sym (A := A)).dualMap.comp pairing := by
  apply SymmetricPower.ext
  intro v
  rw [← sym_eta v]
  apply TensorProduct.ext'
  intro a b
  change tensorPairing (symmetricSection (sym (v 0 ⊗ₜ[ℂ] v 1))) (a ⊗ₜ[ℂ] b)=
    pairing (sym (v 0 ⊗ₜ[ℂ] v 1)) (sym (a ⊗ₜ[ℂ] b))
  rw [symmetricSection_pure, map_add]
  change tensorPairing (v 0 ⊗ₜ[ℂ] v 1) (a ⊗ₜ[ℂ] b)+
    tensorPairing (v 1 ⊗ₜ[ℂ] v 0) (a ⊗ₜ[ℂ] b)=_
  rw [tensorPairing_pure, tensorPairing_pure, pairing_pure]
  ring

theorem pairing_injective : Function.Injective (pairing (A := A)) := by
  intro x y h
  have ht : tensorPairing (symmetricSection x)=tensorPairing (symmetricSection y) := by
    have hx := LinearMap.congr_fun (tensor_identity (A := A)) x
    have hy := LinearMap.congr_fun (tensor_identity (A := A)) y
    change tensorPairing (symmetricSection x)=(sym (A := A)).dualMap (pairing x) at hx
    change tensorPairing (symmetricSection y)=(sym (A := A)).dualMap (pairing y) at hy
    rw [hx, hy, h]
  have hs := congrArg sym (tensorPairing.injective ht)
  rw [sym_section, sym_section] at hs
  have hc := congrArg (fun z => (2 : ℂ)⁻¹ • z) hs
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ)≠0), one_smul] using hc

theorem ranks_equal : Module.finrank ℂ (Sym[ℂ]^2 (Module.Dual ℂ A))=
    Module.finrank ℂ (Module.Dual ℂ (Sym[ℂ]^2 A)) := by
  rw [Subspace.dual_finrank_eq, SymmetricPower.finrank_eq, SymmetricPower.finrank_eq,
    Subspace.dual_finrank_eq]

variable {G : Type*} [Group G] (r : Representation ℂ G A)

def toDual : IntertwiningMap (r.dual.symmetricPower 2) (r.symmetricPower 2).dual where
  toLinearMap := pairing
  isIntertwining' g := by
    apply SymmetricPower.ext
    intro v
    rw [← sym_eta v]
    apply SymmetricPower.ext
    intro w
    rw [← sym_eta w]
    change pairing (SymmetricPower.map (ι := Fin 2) (r.dual g) (sym (v 0 ⊗ₜ[ℂ] v 1)))
      (sym (w 0 ⊗ₜ[ℂ] w 1))=
      pairing (sym (v 0 ⊗ₜ[ℂ] v 1))
        (SymmetricPower.map (ι := Fin 2) (r g⁻¹) (sym (w 0 ⊗ₜ[ℂ] w 1)))
    rw [← SymmetricSquareCauchyRepresentation.sym_natural,
      ← SymmetricSquareCauchyRepresentation.sym_natural, pairing_pure, pairing_pure]
    rfl

/-- The actual dual square, perfect without an irreducibility premise. -/
def equivalence : Representation.Equiv (r.dual.symmetricPower 2) (r.symmetricPower 2).dual :=
  (toDual r).ofBijective ⟨pairing_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := pairing (A := A)) ranks_equal).mp pairing_injective⟩

end
end Math.SymmetricSquareDual
