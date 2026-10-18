import TauCeti.Topology.Algebra.QuadraticForm.RealSpecialOrthogonal
import TauCeti.Topology.Algebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.Norm.Transitivity

/-! The actual realification SU(n) -> SO(2n), with the positive real
Clifford quadratic form and its independent coordinate topology.
This does not itself lift the map into Spin(2n). -/

set_option autoImplicit false
open scoped BigOperators
open Matrix

namespace Math.SpecialUnitaryRealification

noncomputable section

abbrev Source (n : ℕ) := Matrix.specialUnitaryGroup (Fin n) ℂ
abbrev Target (n : ℕ) :=
  TauCeti.QuadraticMap.specialOrthogonalGroup (TauCeti.realCliffordForm (n + n) 0)

def coordinates (n : ℕ) : (Fin (n + n) → ℝ) ≃ₗ[ℝ] (Fin n → ℂ) where
  toFun x i := ⟨x (Fin.castAdd n i), x (Fin.natAdd n i)⟩
  invFun z := Fin.addCases (fun i => (z i).re) (fun i => (z i).im)
  map_add' _ _ := by ext i; rfl
  map_smul' r x := by
    funext i
    apply Complex.ext <;> simp [Complex.real_smul]
  left_inv x := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.addCases_left, Fin.addCases_right]
  right_inv z := by
    funext i
    simp only [Fin.addCases_left, Fin.addCases_right]

theorem form_coordinates (n : ℕ) (x : Fin (n + n) → ℝ) :
    TauCeti.realCliffordForm (n + n) 0 x =
      (star (coordinates n x) ⬝ᵥ coordinates n x).re := by
  simp [TauCeti.realCliffordForm_zero_eq_weightedSumSquares_one,
    QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_add, coordinates,
    dotProduct, Complex.mul_re, Finset.sum_add_distrib]

def complexAction {n : ℕ} (g : Source n) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.UnitaryGroup.toLinearEquiv ⟨g.val, g.property.1⟩

@[simp] theorem complexAction_apply {n : ℕ} (g : Source n) (v : Fin n → ℂ) :
    complexAction g v = g.val *ᵥ v := rfl

def realAction {n : ℕ} (g : Source n) :
    (Fin (n + n) → ℝ) ≃ₗ[ℝ] (Fin (n + n) → ℝ) :=
  ((coordinates n).trans ((complexAction g).restrictScalars ℝ)).trans (coordinates n).symm

theorem coordinates_realAction {n : ℕ} (g : Source n) (v : Fin (n + n) → ℝ) :
    coordinates n (realAction g v) = complexAction g (coordinates n v) :=
  (coordinates n).apply_symm_apply _

theorem preserves_form {n : ℕ} (g : Source n) (v : Fin (n + n) → ℝ) :
    TauCeti.realCliffordForm (n + n) 0 (realAction g v) =
      TauCeti.realCliffordForm (n + n) 0 v := by
  rw [form_coordinates, form_coordinates, coordinates_realAction]
  congr 1
  simp only [complexAction_apply, Matrix.star_mulVec]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have hu : g.val.conjTranspose * g.val = 1 := g.property.1.1
  rw [hu, Matrix.one_mulVec]

theorem realAction_det {n : ℕ} (g : Source n) : LinearEquiv.det (realAction g) = 1 := by
  change LinearEquiv.det (((coordinates n).symm.symm.trans
    ((complexAction g).restrictScalars ℝ)).trans (coordinates n).symm) = 1
  rw [LinearEquiv.det_conj]
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change LinearMap.det ((complexAction g).toLinearMap.restrictScalars ℝ) = 1
  rw [LinearMap.det_restrictScalars]
  change Algebra.norm ℝ (LinearMap.det (Matrix.toLin' g.val)) = 1
  have hd : g.val.det = 1 := g.property.2
  rw [LinearMap.det_toLin', hd, map_one]

def hom (n : ℕ) : Source n →* Target n where
  toFun g := ⟨realAction g, preserves_form g, realAction_det g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply (coordinates n).injective
    simp [coordinates_realAction]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply (coordinates n).injective
    change coordinates n (realAction (g * h) v) =
      coordinates n (realAction g (realAction h v))
    simp only [coordinates_realAction, complexAction_apply, Submonoid.coe_mul,
      Matrix.mulVec_mulVec]

theorem hom_injective (n : ℕ) : Function.Injective (hom n) := by
  classical
  intro g h he
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  have hv := congrArg (fun k : Target n => coordinates n (k.val ((coordinates n).symm v))) he
  change coordinates n (realAction g ((coordinates n).symm v)) =
    coordinates n (realAction h ((coordinates n).symm v)) at hv
  simpa only [Matrix.toLin'_apply, coordinates_realAction, LinearEquiv.apply_symm_apply,
    complexAction_apply] using hv

theorem realAction_continuous_apply (n : ℕ) (v : Fin (n + n) → ℝ) :
    Continuous (fun g : Source n => realAction g v) := by
  change Continuous (fun g : Source n =>
    (coordinates n).symm (g.val *ᵥ coordinates n v))
  apply (coordinates n).symm.toLinearMap.continuous_of_finiteDimensional.comp
  fun_prop

set_option backward.isDefEq.respectTransparency.types false in
theorem hom_continuous (n : ℕ) : Continuous (hom n) := by
  classical
  let : DecidableEq (Fin (n + n + 0)) := Classical.decEq _
  apply (TauCeti.QuadraticMap.isEmbedding_specialOrthogonalToGeneralLinear
    (TauCeti.realCliffordForm (n + n) 0)).isInducing.continuous_iff.mpr
  have h : Continuous ((QuadraticMap.specialOrthogonalToGeneralLinear
      (TauCeti.realCliffordForm (n + n) 0)).comp (hom n)) := by
    apply Continuous.of_coeHom_comp
    apply continuous_matrix
    intro i j
    exact (continuous_apply i).comp (realAction_continuous_apply n (Pi.single j 1))
  exact h

theorem hom_isClosedEmbedding (n : ℕ) : Topology.IsClosedEmbedding (hom n) :=
  (hom_continuous n).isClosedEmbedding (hom_injective n)

end

end Math.SpecialUnitaryRealification
