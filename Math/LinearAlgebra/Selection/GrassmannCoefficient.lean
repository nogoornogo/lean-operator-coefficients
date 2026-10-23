import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! Ordered polynomials in anticommuting coordinate generators and their
unnormalized determinant pairing. No factorial is built into the pairing. -/
namespace Math.GrassmannCoefficient
set_option autoImplicit false
noncomputable section
open Module Set
variable {K M I : Type*} [Field K] [AddCommGroup M] [Module K M]
  [Fintype I] (b : Basis I K M) (n : ℕ)

def coordinateProduct (j : Fin n → I) : MultilinearMap K (fun _ : Fin n => M) K :=
  (MultilinearMap.mkPiAlgebra K (Fin n) K).compLinearMap (fun i => b.coord (j i))

def coordinateExpansion (F : MultilinearMap K (fun _ : Fin n => M) K) :=
  ∑ j : Fin n → I, F (fun i => b (j i)) • coordinateProduct b n j

theorem coordinateExpansion_eq (F : MultilinearMap K (fun _ : Fin n => M) K) :
    coordinateExpansion b n F = F := by
  classical
  apply Basis.ext_multilinear (fun _ => b)
  intro j
  simp only [coordinateExpansion, sum_apply,
    smul_apply, coordinateProduct, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Basis.coord_apply, Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul]
  have hp (k : Fin n → I) :
      (∏ i, if j i = k i then (1 : K) else 0) = if k = j then 1 else 0 := by
    by_cases h : k = j
    · simp [h]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right (Ne.symm hi))]
      simp [h]
  simp_rw [hp]
  simp

/-- The explicit ordered sum of products of Grassmann coordinate generators. -/
def polynomial (F : MultilinearMap K (fun _ : Fin n => M) K) :
    ⋀[K]^n (Module.Dual K M) :=
  ∑ j : Fin n → I, F (fun i => b (j i)) •
    exteriorPower.ιMulti K n (fun i => b.coord (j i))

/-- In the full exterior algebra this is literally the ordered product of
coordinate generators, without division by a factorial. -/
theorem polynomial_generators (F : MultilinearMap K (fun _ : Fin n => M) K) :
    (polynomial b n F : ExteriorAlgebra K (Module.Dual K M)) =
      ∑ j : Fin n → I, F (fun i => b (j i)) •
        (List.ofFn (fun i => ExteriorAlgebra.ι K (b.coord (j i)))).prod := by
  simp [polynomial, ExteriorAlgebra.ιMulti_apply]

theorem polynomial_pairing (F : MultilinearMap K (fun _ : Fin n => M) K)
    (v : Fin n → M) :
    exteriorPower.pairingDual K M n (polynomial b n F)
      (exteriorPower.ιMulti K n v) = F.alternatization v := by
  classical
  rw [← coordinateExpansion_eq b n F]
  simp only [polynomial, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, exteriorPower.pairingDual_ιMulti_ιMulti]
  rw [coordinateExpansion_eq]
  simp only [Matrix.det_apply, Matrix.of_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [MultilinearMap.alternatization_apply]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [MultilinearMap.domDomCongr_apply]
  have he := congrArg (fun G : MultilinearMap K (fun _ : Fin n => M) K =>
    G (v ∘ p)) (coordinateExpansion_eq b n F)
  simp only [coordinateExpansion, sum_apply,
    smul_apply, coordinateProduct, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Function.comp_apply, smul_eq_mul] at he
  simp only [Function.comp_def] at he
  rw [← he, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Units.smul_def, mul_comm, mul_left_comm, mul_assoc]

variable [LinearOrder I]

/-- Finite-dimensional Grassmann polynomials and exterior functionals are
canonically equivalent through the determinant pairing. -/
def pairingEquiv : ⋀[K]^n (Module.Dual K M) ≃ₗ[K] Module.Dual K (⋀[K]^n M) := by
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  exact LinearEquiv.ofBijective (exteriorPower.pairingDual K M n)
    (exteriorPower.bijective_pairingDual K M n)

omit [LinearOrder I] in
@[simp] theorem pairingEquiv_apply (P : ⋀[K]^n (Module.Dual K M)) :
    pairingEquiv b n P = exteriorPower.pairingDual K M n P := rfl

/-- Sorted monomial coefficients are evaluations on the corresponding wedge
of basis vectors. This fixes the generator-order convention explicitly. -/
theorem polynomial_coordinate (F : MultilinearMap K (fun _ : Fin n => M) K)
    (s : powersetCard I n) :
    (b.dualBasis.exteriorPower n).repr (polynomial b n F) s =
      F.alternatization (b ∘ s.1.orderEmbOfFin s.2) := by
  classical
  have hc : (b.dualBasis.exteriorPower n).coord s =
      (LinearMap.applyₗ (b.exteriorPower n s)).comp
        (exteriorPower.pairingDual K M n) := by
    apply (b.dualBasis.exteriorPower n).ext
    intro t
    change (b.dualBasis.exteriorPower n).coord s ((b.dualBasis.exteriorPower n) t) =
      exteriorPower.pairingDual K M n ((b.dualBasis.exteriorPower n) t)
        (b.exteriorPower n s)
    rw [exteriorPower.pairingDual_apply_dualBasis_exteriorPower]
    simp only [Basis.coord_apply, Basis.repr_self, Basis.dualBasis_apply_self,
      Finsupp.single_apply]
    simp [eq_comm]
  rw [← Basis.coord_apply, hc]
  change exteriorPower.pairingDual K M n (polynomial b n F)
    (b.exteriorPower n s) = _
  rw [exteriorPower.basis_apply]
  exact polynomial_pairing b n F _

end
end Math.GrassmannCoefficient
