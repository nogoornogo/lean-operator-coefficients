import Math.LinearAlgebra.SymmetricPurePowers
import Math.RepresentationTheory.SymmetricMultilinearDiagonal
import TauCeti.RepresentationTheory.ExteriorPower
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RepresentationTheory.Irreducible

/-! The top-column Cauchy map, constructed by finite symmetrization.
No Schur decomposition or branching premise is supplied. -/
namespace Math.TopExteriorCauchy
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] {n : ℕ}

def raw (a : Fin n → A) :
    MultilinearMap ℂ (fun _ : Fin n => B) (⋀[ℂ]^n (A ⊗[ℂ] B)) :=
  (exteriorPower.ιMulti ℂ n).toMultilinearMap.compLinearMap
    (fun i => TensorProduct.mk ℂ A B (a i))

def map (a : Fin n → A) : Sym[ℂ]^n B →ₗ[ℂ] ⋀[ℂ]^n (A ⊗[ℂ] B) :=
  SymmetricPowerDescent.lift n (SymmetricMultilinearProjection.project n (raw a))

theorem diagonal (a : Fin n → A) (v : B) :
    map a (SymmetricPower.tprod ℂ (fun _ : Fin n => v)) =
      exteriorPower.ιMulti ℂ n (fun i => a i ⊗ₜ[ℂ] v) := by
  exact SymmetricMultilinearProjection.lift_project_diagonal n (raw a) v

theorem natural (a : Fin n → A) (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B) :
    (exteriorPower.map n (TensorProduct.map f g)).comp (map a) =
      (map (f ∘ a)).comp (SymmetricPower.map (ι := Fin n) g) := by
  apply SymmetricPurePowers.ext
  intro v
  simp only [LinearMap.comp_apply, diagonal, exteriorPower.map_apply_ιMulti,
    SymmetricPower.map_tprod, Function.comp_def, TensorProduct.map_tmul]

theorem basis_change (b : Module.Basis (Fin n) ℂ A) (f : A →ₗ[ℂ] A) :
    map (B := B) (f ∘ b) = LinearMap.det f • map b := by
  apply SymmetricPurePowers.ext
  intro v
  rw [diagonal, LinearMap.smul_apply, diagonal]
  have he := LinearMap.congr_fun (exteriorPower.map_top_eq_det_smul b f)
    (exteriorPower.ιMulti ℂ n b)
  have hh := congrArg (exteriorPower.map n ((TensorProduct.mk ℂ A B).flip v)) he
  simpa only [exteriorPower.map_apply_ιMulti, Function.comp_def, map_smul,
    LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.mk_apply,
    LinearMap.flip_apply] using hh

def evaluate (φ : Module.Dual ℂ B) : A ⊗[ℂ] B →ₗ[ℂ] A :=
  (TensorProduct.rid ℂ A).toLinearMap.comp
    (TensorProduct.map (LinearMap.id) φ)

@[simp] theorem evaluate_tmul (φ : Module.Dual ℂ B) (a : A) (v : B) :
    evaluate φ (a ⊗ₜ[ℂ] v) = φ v • a := by
  simp [evaluate]

theorem diagonal_nonzero (b : Module.Basis (Fin n) ℂ A) (v : B)
    (φ : Module.Dual ℂ B) (hv : φ v = 1) :
    map b (SymmetricPower.tprod ℂ (fun _ : Fin n => v)) ≠ 0 := by
  intro he
  have hh := congrArg (exteriorPower.map n (evaluate (A := A) φ)) he
  rw [diagonal, exteriorPower.map_apply_ιMulti] at hh
  simp only [Function.comp_def, evaluate_tmul, hv, one_smul, map_zero] at hh
  have htop := congrArg (exteriorPower.topEquiv b) hh
  simp only [exteriorPower.topEquiv_apply_ιMulti, Module.Basis.det_self, map_zero,
    one_ne_zero] at htop

theorem nonzero (b : Module.Basis (Fin n) ℂ A) (v : B)
    (φ : Module.Dual ℂ B) (hv : φ v = 1) : map (B := B) b ≠ 0 := by
  intro he
  exact diagonal_nonzero b v φ hv (by rw [he]; rfl)

variable {G : Type*} [Group G]

/-- A determinant-one factor supplies the top-column Cauchy intertwiner. -/
def intertwiner (b : Module.Basis (Fin n) ℂ A)
    (a : Representation ℂ G A) (r : Representation ℂ G B)
    (ha : ∀ g, LinearMap.det (a g) = 1) :
    IntertwiningMap (r.symmetricPower n) ((a.tprod r).exteriorPower n) where
  toLinearMap := map b
  isIntertwining' g := by
    have he := natural (B := B) b (a g) (r g)
    rw [basis_change, ha g, one_smul] at he
    exact he.symm

theorem intertwiner_nonzero (b : Module.Basis (Fin n) ℂ A)
    (a : Representation ℂ G A) (r : Representation ℂ G B)
    (ha : ∀ g, LinearMap.det (a g) = 1)
    (v : B) (φ : Module.Dual ℂ B) (hv : φ v = 1) :
    intertwiner b a r ha ≠ 0 := by
  intro he
  exact nonzero b v φ hv (congrArg IntertwiningMap.toLinearMap he)

theorem intertwiner_injective (b : Module.Basis (Fin n) ℂ A)
    (a : Representation ℂ G A) (r : Representation ℂ G B)
    (ha : ∀ g, LinearMap.det (a g) = 1) [IsIrreducible (r.symmetricPower n)]
    (v : B) (φ : Module.Dual ℂ B) (hv : φ v = 1) :
    Function.Injective (intertwiner b a r ha) :=
  (IsIrreducible.injective_or_eq_zero (intertwiner b a r ha)).resolve_right
    (intertwiner_nonzero b a r ha v φ hv)

end
end Math.TopExteriorCauchy
