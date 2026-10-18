import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Character

/-! Finite copies and Hom multiplicities of an explicitly specified spectrum.
These constructions do not prescribe an action on the multiplicity spaces. -/

namespace Math.FiniteSpectrum
noncomputable section
open Representation

variable {G U V W : Type*} [Group G]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def copies (n : ℕ) (rho : Representation ℂ G V) :
    Representation ℂ G (Fin n → V) where
  toFun g := LinearMap.pi fun i => (rho g).comp (LinearMap.proj i)
  map_one' := by ext x i; simp
  map_mul' g h := by ext x i; simp [map_mul]

@[simp] theorem copies_apply (n : ℕ) (rho : Representation ℂ G V)
    (g : G) (x : Fin n → V) (i : Fin n) : copies n rho g x i = rho g (x i) := rfl

theorem character_copies [FiniteDimensional ℂ V] (n : ℕ)
    (rho : Representation ℂ G V) (g : G) :
    (copies n rho).character g = (n : ℂ) * rho.character g := by
  classical
  let b := Module.finBasis ℂ V
  simp only [Representation.character]
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis fun _ : Fin n => b),
    LinearMap.trace_eq_matrix_trace ℂ b]
  simp [Matrix.trace, LinearMap.toMatrix_apply', Pi.basis_apply, Pi.basis_repr,
    copies_apply, Fintype.sum_sigma]

def homProd (rho : Representation ℂ G U) (sigma : Representation ℂ G V)
    (tau : Representation ℂ G W) :
    IntertwiningMap rho (sigma.prod tau) ≃ₗ[ℂ]
      (IntertwiningMap rho sigma × IntertwiningMap rho tau) where
  toFun f := ((IntertwiningMap.fst ℂ sigma tau).comp f,
    (IntertwiningMap.snd ℂ sigma tau).comp f)
  invFun f := f.1.prod f.2
  left_inv f := by ext x <;> rfl
  right_inv f := by rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def homCopies (n : ℕ) (rho : Representation ℂ G U) (sigma : Representation ℂ G V) :
    IntertwiningMap rho (copies n sigma) ≃ₗ[ℂ] (Fin n → IntertwiningMap rho sigma) where
  toFun f i :=
    { toLinearMap := (LinearMap.proj i).comp f.toLinearMap
      isIntertwining' g := by
        ext x
        exact congrFun (LinearMap.congr_fun (f.isIntertwining' g) x) i }
  invFun f :=
    { toLinearMap := LinearMap.pi fun i => (f i).toLinearMap
      isIntertwining' g := by
        ext x i
        exact LinearMap.congr_fun ((f i).isIntertwining' g) x }
  left_inv f := by ext x i; rfl
  right_inv f := by rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def homCongrRight (rho : Representation ℂ G U)
    {sigma : Representation ℂ G V} {tau : Representation ℂ G W}
    (e : Representation.Equiv sigma tau) :
    IntertwiningMap rho sigma ≃ₗ[ℂ] IntertwiningMap rho tau where
  toFun f := e.toIntertwiningMap.comp f
  invFun f := e.symm.toIntertwiningMap.comp f
  left_inv f := by ext x; exact e.toLinearEquiv.symm_apply_apply (f x)
  right_inv f := by ext x; exact e.toLinearEquiv.apply_symm_apply (f x)
  map_add' _ _ := by ext x; exact map_add e _ _
  map_smul' _ _ := by ext x; exact map_smul e _ _

theorem hom_finrank_prod [FiniteDimensional ℂ U] [FiniteDimensional ℂ V]
    [FiniteDimensional ℂ W] (rho : Representation ℂ G U)
    (sigma : Representation ℂ G V) (tau : Representation ℂ G W) :
    Module.finrank ℂ (IntertwiningMap rho (sigma.prod tau)) =
      Module.finrank ℂ (IntertwiningMap rho sigma) +
      Module.finrank ℂ (IntertwiningMap rho tau) := by
  rw [(homProd rho sigma tau).finrank_eq, Module.finrank_prod]

theorem hom_finrank_copies [FiniteDimensional ℂ U] [FiniteDimensional ℂ V]
    (n : ℕ) (rho : Representation ℂ G U)
    (sigma : Representation ℂ G V) :
    Module.finrank ℂ (IntertwiningMap rho (copies n sigma)) =
      n * Module.finrank ℂ (IntertwiningMap rho sigma) := by
  rw [(homCopies n rho sigma).finrank_eq, Module.finrank_pi_fintype]
  simp

theorem intertwiner_eq_zero_of_scalar (rho : Representation ℂ G U)
    (sigma : Representation ℂ G V) (g : G) (a b : ℂ)
    (hr : ∀ x, rho g x = a • x) (hs : ∀ y, sigma g y = b • y)
    (hab : a ≠ b) (f : IntertwiningMap rho sigma) : f = 0 := by
  ext x
  have he := LinearMap.congr_fun (f.isIntertwining' g) x
  change f (rho g x) = sigma g (f x) at he
  rw [hr, hs, map_smul] at he
  have hz : (a - b) • f x = 0 := by rw [sub_smul, he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab)

end
end Math.FiniteSpectrum
