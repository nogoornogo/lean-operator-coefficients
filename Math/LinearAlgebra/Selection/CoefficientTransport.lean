import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Analysis.Complex.Basic

/-! Transport finite families of vector coefficients along a linear map of
free label spaces. This is the coordinate tensor-product functor. -/
namespace Math.CoefficientTransport
set_option autoImplicit false
noncomputable section
variable {J K L V W U : Type*}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

/-- A numerical vector times a vector coefficient. -/
def spread (v : J →₀ ℂ) : V →ₗ[ℂ] (J →₀ V) where
  toFun a := v.sum (fun j c => Finsupp.single j (c • a))
  map_add' a b := by simp [Finsupp.sum, smul_add, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finsupp.sum, smul_comm c, Finset.smul_sum]

@[simp] theorem spread_apply (v : J →₀ ℂ) (a : V) (j : J) :
    spread v a j = v j • a := by
  classical
  simp only [spread, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single j (by intro k hk hne; simp [hne]) (by simp)]
  simp

@[simp] theorem spread_zero (a : V) : spread (0 : J →₀ ℂ) a = 0 := by ext j; simp

theorem spread_add (v w : J →₀ ℂ) (a : V) : spread (v+w) a = spread v a+spread w a := by
  ext j; simp [add_smul]

@[simp] theorem spread_smul (c : ℂ) (v : J →₀ ℂ) (a : V) :
    spread (c • v) a = c • spread v a := by ext j; simp [smul_smul]

@[simp] theorem spread_single (j : J) (c : ℂ) (a : V) :
    spread (Finsupp.single j c) a = Finsupp.single j (c • a) := by
  simp [spread]

def push (T : (J →₀ ℂ) →ₗ[ℂ] (K →₀ ℂ)) (r : V →ₗ[ℂ] W) :
    (J →₀ V) →ₗ[ℂ] (K →₀ W) :=
  Finsupp.lsum ℂ (fun j => (spread (T (Finsupp.single j 1))).comp r)

@[simp] theorem push_single (T : (J →₀ ℂ) →ₗ[ℂ] (K →₀ ℂ)) (r : V →ₗ[ℂ] W)
    (j : J) (a : V) : push T r (Finsupp.single j a) = spread (T (Finsupp.single j 1)) (r a) := by
  simp [push]

@[simp] theorem push_spread (T : (J →₀ ℂ) →ₗ[ℂ] (K →₀ ℂ)) (r : V →ₗ[ℂ] W)
    (v : J →₀ ℂ) (a : V) : push T r (spread v a) = spread (T v) (r a) := by
  induction v using Finsupp.induction_linear with
  | zero => ext j; simp
  | add v w hv hw =>
    rw [spread_add,map_add,hv,hw,map_add,spread_add]
  | single j c =>
    rw [spread_single,push_single,map_smul]
    have he : T (Finsupp.single j c) = c • T (Finsupp.single j 1) := by
      rw [← map_smul]; congr 1; simp
    rw [he,spread_smul,map_smul]

theorem push_comp (T : (J →₀ ℂ) →ₗ[ℂ] (K →₀ ℂ))
    (S : (K →₀ ℂ) →ₗ[ℂ] (L →₀ ℂ)) (r : V →ₗ[ℂ] W) (s : W →ₗ[ℂ] U) :
    (push S s).comp (push T r) = push (S.comp T) (s.comp r) := by
  apply Finsupp.lhom_ext
  intro j a
  simp

@[simp] theorem push_id : push (LinearMap.id : (J →₀ ℂ) →ₗ[ℂ] _) (LinearMap.id : V →ₗ[ℂ] V) =
    LinearMap.id := by
  apply Finsupp.lhom_ext
  intro j a
  simp

@[simp] theorem push_identity_apply (r : V →ₗ[ℂ] W) (v : J →₀ V) (j : J) :
    push LinearMap.id r v j = r (v j) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,Finsupp.add_apply,hv,hw]
  | single k a => by_cases h : k=j <;> simp [h]

theorem push_apply (T : (J →₀ ℂ) →ₗ[ℂ] (K →₀ ℂ)) (r : V →ₗ[ℂ] W)
    (v : J →₀ V) (k : K) :
    push T r v k = v.sum (fun j a => T (Finsupp.single j 1) k • r a) := by
  simp [push,Finsupp.lsum_apply,Finsupp.sum_apply]

/-- A coordinate-dependent linear operation on coefficients. -/
def diagonal (f : J → V →ₗ[ℂ] W) : (J →₀ V) →ₗ[ℂ] (J →₀ W) :=
  Finsupp.lsum ℂ (fun j => (Finsupp.lsingle j).comp (f j))

@[simp] theorem diagonal_single (f : J → V →ₗ[ℂ] W) (j : J) (a : V) :
    diagonal f (Finsupp.single j a) = Finsupp.single j (f j a) := by simp [diagonal]

@[simp] theorem diagonal_apply (f : J → V →ₗ[ℂ] W) (v : J →₀ V) (j : J) :
    diagonal f v j = f j (v j) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,Finsupp.add_apply,hv,hw]
  | single k a => by_cases h : k=j <;> simp [h]

end
end Math.CoefficientTransport
