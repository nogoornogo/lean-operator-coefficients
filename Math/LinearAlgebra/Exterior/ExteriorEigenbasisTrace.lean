import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.Basic.Complex.Basic

/-! Trace of exterior powers from a supplied eigenbasis. No group or
torus polynomiality assumption enters this finite-dimensional calculation. -/

set_option autoImplicit false

namespace Math.ExteriorEigenbasisTrace

noncomputable section

variable {I V : Type*} [Fintype I] [LinearOrder I] [AddCommGroup V] [Module ℂ V]
  (b : Module.Basis I ℂ V) (f : V →ₗ[ℂ] V) (w : I → ℂ)
  (he : ∀ i, f (b i) = w i • b i)

include b he in
theorem trace_eq_sum : LinearMap.trace ℂ V f = ∑ i, w i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b f, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.diag, LinearMap.toMatrix_apply, he, b.repr_self]

omit [Fintype I] in
theorem product_ordered {M : Type*} [CommMonoid M] {d : ℕ}
    (s : Set.powersetCard I d) (a : I → M) :
    (∏ j : Fin d, a (Set.powersetCard.ofFinEmbEquiv.symm s j)) = ∏ i ∈ s.val, a i := by
  change (∏ j : Fin d, a (s.val.orderEmbOfFin (Set.powersetCard.card_eq s) j)) = _
  let e := (s.val.orderEmbOfFin (Set.powersetCard.card_eq s)).toEmbedding
  calc
    _ = ∏ j ∈ (Finset.univ : Finset (Fin d)), a (e j) := rfl
    _ = ∏ i ∈ Finset.map e Finset.univ, a i := (Finset.prod_map _ e a).symm
    _ = _ := by rw [Finset.map_orderEmbOfFin_univ]

omit [Fintype I] in
include he in
theorem exterior_eigen (d : ℕ) (s : Set.powersetCard I d) :
    exteriorPower.map d f (b.exteriorPower d s) =
      (∏ i ∈ s.val, w i) • b.exteriorPower d s := by
  rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family]
  change exteriorPower.ιMulti ℂ d
    (fun j => f (b (Set.powersetCard.ofFinEmbEquiv.symm s j))) = _
  simp_rw [he]
  rw [AlternatingMap.map_smul_univ, product_ordered s w]
  rfl

include b he in
theorem exterior_trace (d : ℕ) :
    LinearMap.trace ℂ (⋀[ℂ]^d V) (exteriorPower.map d f) =
      ∑ s : Set.powersetCard I d, ∏ i ∈ s.val, w i := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (b.exteriorPower d) _, Matrix.trace]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Matrix.diag, LinearMap.toMatrix_apply, exterior_eigen b f w he,
    map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]

omit [Fintype I] in
include he in
theorem algebra_eigen (s : Finset I) :
    ExteriorAlgebra.map f (b.ExteriorAlgebra s) =
      (∏ i ∈ s, w i) • b.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (s_card := rfl)]
  unfold ExteriorAlgebra.ιMulti_family
  rw [ExteriorAlgebra.map_apply_ιMulti]
  change ExteriorAlgebra.ιMulti ℂ s.card
    (fun j => f (b (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard rfl) j))) = _
  simp_rw [he]
  rw [AlternatingMap.map_smul_univ, product_ordered]
  rfl

end

end Math.ExteriorEigenbasisTrace
