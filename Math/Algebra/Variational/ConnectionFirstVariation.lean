import Math.Algebra.Jets.MatrixTraceIBP
import Math.Algebra.Constructions.FormalGaugeTransformation
import Mathlib.Tactic

/-! Curvature first variation, derived from actual commuting variation and
ordinary Leibniz maps. No variational equation is assumed. -/
namespace Math.FormalConnection
set_option autoImplicit false
noncomputable section
variable {A I : Type*} [Ring A] [Algebra ℂ A]
  (P : Ordinary I A) (C : I → A) (V : A →ₗ[ℂ] A)
  (hV : ∀ x y, V (x * y) = V x * y + x * V y)
  (hD : ∀ i x, V (P.d i x) = P.d i (V x))

include hV hD in
theorem curvature_variation (i j : I) :
    V (curvature P C i j) = covariant P C i (V (C j)) - covariant P C j (V (C i)) := by
  simp only [curvature, bracket, covariant_apply, map_add, map_sub, hV, hD]
  noncomm_ring

end
end Math.FormalConnection

namespace Math.MatrixFirstVariation
set_option autoImplicit false
noncomputable section
open FormalConnection
variable {A I N : Type*} [CommRing A] [Algebra ℂ A]
  [Fintype I] [Fintype N] [DecidableEq N]
  (D : I → Derivation ℂ A A) (hc : ∀ i j p, D i (D j p) = D j (D i p))
  (C : I → Matrix N N A) (V : Derivation ℂ A A)
  (hVD : ∀ i p, V (D i p) = D i (V p))

def matrixVariation : Matrix N N A →ₗ[ℂ] Matrix N N A := V.toLinearMap.mapMatrix
def eta (i : I) := matrixVariation V (C i)
abbrev P : Ordinary I (Matrix N N A) := MatrixTraceIBP.ordinary D hc
def F (i j : I) := curvature (P D hc) C i j
def T (i j : I) := Matrix.trace (covariant (P D hc) C i (eta C V j) * F D hc C i j)

theorem matrixVariation_mul (x y : Matrix N N A) :
    matrixVariation V (x * y) = matrixVariation V x * y + x * matrixVariation V y :=
  (MatrixTraceIBP.ordinary (fun _ : Unit => V) (fun _ _ _ => rfl)).mul () x y

omit [Fintype I] in
include hVD in
theorem matrixVariation_commute (i : I) (x : Matrix N N A) :
    matrixVariation V ((P D hc).d i x) = (P D hc).d i (matrixVariation V x) := by
  apply Matrix.ext
  intro a b
  exact hVD i (x a b)

omit [DecidableEq N] in
theorem variation_trace (x : Matrix N N A) : V (Matrix.trace x) = Matrix.trace (matrixVariation V x) := by
  change V (∑ a, x a a) = ∑ a, V (x a a)
  exact map_sum _ _ _

omit [Fintype I] in
include hVD in
theorem variation_curvature (i j : I) : matrixVariation V (F D hc C i j) =
    covariant (P D hc) C i (eta C V j) - covariant (P D hc) C j (eta C V i) :=
  curvature_variation _ _ _ (matrixVariation_mul V) (matrixVariation_commute D hc V hVD) i j

omit [Fintype I] in
include hVD in
theorem variation_density (i j : I) : V (Matrix.trace (F D hc C i j * F D hc C i j)) =
    (2 : ℂ) • (T D hc C V i j + T D hc C V j i) := by
  rw [variation_trace, matrixVariation_mul, Matrix.trace_add,
    Matrix.trace_mul_comm (F D hc C i j), variation_curvature D hc C V hVD]
  have hs : F D hc C i j = -F D hc C j i := curvature_skew _ _ _ _
  dsimp only [T]
  simp only [sub_mul, Matrix.trace_sub]
  rw [hs]
  simp only [mul_neg, Matrix.trace_neg]
  module

def contraction (s : I → ℂ) : A :=
  ∑ i, ∑ j, (s i * s j) • Matrix.trace (F D hc C i j * F D hc C i j)

def boundary (s : I → ℂ) (i : I) : A :=
  -∑ j, (s i * s j) • Matrix.trace (eta C V j * F D hc C i j)

def bulk (s : I → ℂ) : A :=
  ∑ j, s j • Matrix.trace (eta C V j * signedEquation (P D hc) C s j)

def lagrangian (s : I → ℂ) : A := -(1 / 4 : ℂ) • contraction D hc C s

theorem variation_smul (c : ℂ) (x : A) : V (c • x) = c • V x := V.toLinearMap.map_smul c x
omit [Fintype I] in
theorem ordinary_smul (i : I) (c : ℂ) (x : A) : D i (c • x) = c • D i x :=
  (D i).toLinearMap.map_smul c x

theorem swapped_sum (s : I → ℂ) (t : I → I → A) :
    (∑ i, ∑ j, (s i * s j) • t j i) = ∑ i, ∑ j, (s i * s j) • t i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm (s j) (s i)]

include hVD in
theorem variation_contraction (s : I → ℂ) : V (contraction D hc C s) =
    (4 : ℂ) • (∑ i, ∑ j, (s i * s j) • T D hc C V i j) := by
  calc
    V (contraction D hc C s) = ∑ i, ∑ j, (2 : ℂ) •
        ((s i * s j) • T D hc C V i j + (s i * s j) • T D hc C V j i) := by
      simp only [contraction, map_sum, variation_smul, variation_density D hc C V hVD]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      module
    _ = (2 : ℂ) • ((∑ i, ∑ j, (s i * s j) • T D hc C V i j) +
        ∑ i, ∑ j, (s i * s j) • T D hc C V j i) := by
      simp only [Finset.smul_sum, smul_add, Finset.sum_add_distrib]
    _ = _ := by rw [swapped_sum]; module

theorem bulk_expansion (s : I → ℂ) : bulk D hc C V s =
    ∑ i, ∑ j, (s i * s j) • Matrix.trace (eta C V j * covariant (P D hc) C i (F D hc C i j)) := by
  simp only [bulk, signedEquation, Matrix.mul_sum, mul_smul_comm, Matrix.trace_sum,
    Matrix.trace_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm (s j) (s i)]
  rfl

theorem boundary_expansion (s : I → ℂ) :
    ∑ i, D i (boundary D hc C V s i) =
      -(∑ i, ∑ j, (s i * s j) • T D hc C V i j) - bulk D hc C V s := by
  have ht (i j : I) := MatrixTraceIBP.trace_ibp D hc C i (eta C V j) (F D hc C i j)
  rw [bulk_expansion]
  simp only [boundary, map_neg, map_sum, ordinary_smul, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, sub_eq_add_neg]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← ht i j]
  dsimp [T]
  module

include hVD in
theorem first_variation (s : I → ℂ) : V (lagrangian D hc C s) =
    bulk D hc C V s + ∑ i, D i (boundary D hc C V s i) := by
  rw [lagrangian, variation_smul, variation_contraction D hc C V hVD, boundary_expansion]
  module

end
end Math.MatrixFirstVariation
