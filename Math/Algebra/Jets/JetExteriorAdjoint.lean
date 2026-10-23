import Math.LinearAlgebra.Exterior.ExteriorHermitianConjugation
import PhyslibAlpha.Mathematics.ExteriorAlgebra
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! Hermitian conjugation commutes with even formal derivatives and descends
through their linear divergence range. No product on the IBP quotient is used. -/
namespace Math.JetExteriorAdjoint
set_option autoImplicit false
noncomputable section
open ExteriorHermitianConjugation
variable {V I : Type*} [AddCommGroup V] [Module ℂ V]
  (c : V →ₛₗ[starRingEnd ℂ] V) (D : I → V →ₗ[ℂ] V)

def map : ExteriorAlgebra ℂ V →ₛₗ[starRingEnd ℂ] ExteriorAlgebra ℂ V where
  toFun := adjoint c
  map_add' x y := by simp [adjoint]
  map_smul' z x := adjoint_smul c z x

@[simp] theorem map_generator (v : V) : map c (ExteriorAlgebra.ι ℂ v) = ExteriorAlgebra.ι ℂ (c v) := by
  change adjoint c _ = _
  simp [adjoint]

@[simp] theorem map_scalar (z : ℂ) : map c (algebraMap ℂ (ExteriorAlgebra ℂ V) z) =
    algebraMap ℂ _ (star z) := by
  change adjoint c _ = _
  simp [adjoint]

theorem map_mul (x y : ExteriorAlgebra ℂ V) : map c (x * y) = map c y * map c x := adjoint_mul c x y

theorem involutive (hc : ∀ v, c (c v) = v) (x : ExteriorAlgebra ℂ V) : map c (map c x) = x :=
  adjoint_involutive c hc x

theorem naturality {W : Type*} [AddCommGroup W] [Module ℂ W]
    (cW : W →ₛₗ[starRingEnd ℂ] W) (f : V →ₗ[ℂ] W) (h : ∀ v, f (c v) = cW (f v))
    (x : ExteriorAlgebra ℂ V) :
    ExteriorAlgebra.map f (map c x) = map cW (ExteriorAlgebra.map f x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap z => simp only [map_scalar, AlgHom.commutes]
  | ι v => simp only [map_generator, ExteriorAlgebra.map_apply_ι, h]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, _root_.map_mul, hx, hy]

theorem derivative (h : ∀ i v, c (D i v) = D i (c v)) (i : I) (x : ExteriorAlgebra ℂ V) :
    map c (ExteriorAlgebra.derivationOfLinear (D i) x) =
      ExteriorAlgebra.derivationOfLinear (D i) (map c x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap z => rw [ExteriorAlgebra.derivationOfLinear_algebraMap, map_zero, map_scalar,
      ExteriorAlgebra.derivationOfLinear_algebraMap]
  | ι v => simp only [ExteriorAlgebra.derivationOfLinear_ι, map_generator, h]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy =>
    simp only [ExteriorAlgebra.derivationOfLinear_mul, map_add, map_mul, hx, hy]
    abel

def divergence : (I →₀ ExteriorAlgebra ℂ V) →ₗ[ℂ] ExteriorAlgebra ℂ V :=
  Finsupp.lsum ℂ (fun i => ExteriorAlgebra.derivationOfLinear (D i))

@[simp] theorem divergence_single (i : I) (x : ExteriorAlgebra ℂ V) :
    divergence D (Finsupp.single i x) = ExteriorAlgebra.derivationOfLinear (D i) x :=
  Finsupp.lsum_single ℂ _ i x

def relations : Submodule ℂ (ExteriorAlgebra ℂ V) := (divergence D).range

theorem stable (h : ∀ i v, c (D i v) = D i (c v)) {x : ExteriorAlgebra ℂ V}
    (hx : x ∈ relations D) : map c x ∈ relations D := by
  obtain ⟨a, rfl⟩ := hx
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simpa only [map_add] using (relations D).add_mem ha hb
  | single i x =>
    rw [divergence_single]
    rw [derivative c D h]
    exact ⟨Finsupp.single i (map c x), Finsupp.lsum_single ℂ _ i _⟩

def quotient (h : ∀ i v, c (D i v) = D i (c v)) :
    (ExteriorAlgebra ℂ V ⧸ relations D) →ₛₗ[starRingEnd ℂ] (ExteriorAlgebra ℂ V ⧸ relations D) :=
  (relations D).mapQ (relations D) (map c) (fun _ hx => stable c D h hx)

@[simp] theorem quotient_mk (h : ∀ i v, c (D i v) = D i (c v)) (x : ExteriorAlgebra ℂ V) :
    quotient c D h ((relations D).mkQ x) = (relations D).mkQ (map c x) := rfl

theorem quotient_involutive (h : ∀ i v, c (D i v) = D i (c v)) (hc : ∀ v, c (c v) = v)
    (x : ExteriorAlgebra ℂ V ⧸ relations D) : quotient c D h (quotient c D h x) = x := by
  obtain ⟨x, rfl⟩ := (relations D).mkQ_surjective x
  rw [quotient_mk, quotient_mk, involutive c hc]

end
end Math.JetExteriorAdjoint
