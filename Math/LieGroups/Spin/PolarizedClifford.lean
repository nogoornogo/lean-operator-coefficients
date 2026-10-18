import Math.LieGroups.Spin.CompactGroup
import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The positive real Clifford algebra acts through a complex polarized
quadratic space. This is a map from the actual compact real carrier, not
an identification of compact and split real Spin groups. -/

set_option autoImplicit false

namespace Math.CompactSpin.Polarized

noncomputable section

open CliffordAlgebra

abbrev RealSpace (n : ℕ) := Fin (n + n) → ℝ
abbrev realForm (n : ℕ) := TauCeti.realCliffordForm (n + n) 0
abbrev complexForm (n : ℕ) := TauCeti.splitEvenForm ℂ n

def complexCoordinates (n : ℕ) (s : ℂ) : RealSpace n →ₗ[ℝ] (Fin n → ℂ) where
  toFun v i := (v (Fin.castAdd n i) : ℂ) + s * (v (Fin.natAdd n i) : ℂ)
  map_add' v w := by ext i; simp; ring
  map_smul' r v := by ext i; simp [Complex.real_smul]; ring

def coordinates (n : ℕ) : RealSpace n →ₗ[ℝ] TauCeti.SplitEvenSpace ℂ n :=
  (((dotProductBilin ℂ ℂ).restrictScalars ℝ).comp (complexCoordinates n (-Complex.I))).prod
    (complexCoordinates n Complex.I)

theorem coordinates_injective (n : ℕ) : Function.Injective (coordinates n) := by
  intro v w h
  have hc (j : Fin n) :
      (v (Fin.castAdd n j) : ℂ) + Complex.I * (v (Fin.natAdd n j) : ℂ) =
      (w (Fin.castAdd n j) : ℂ) + Complex.I * (w (Fin.natAdd n j) : ℂ) :=
    congrArg (fun x : TauCeti.SplitEvenSpace ℂ n => x.2 j) h
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa using congrArg Complex.re (hc j)
  · simpa using congrArg Complex.im (hc j)

theorem coordinates_form (n : ℕ) (v : RealSpace n) :
    complexForm n (coordinates n v) = (realForm n v : ℂ) := by
  change (∑ i, ((v (Fin.castAdd n i) : ℂ) + -Complex.I * (v (Fin.natAdd n i) : ℂ)) *
    ((v (Fin.castAdd n i) : ℂ) + Complex.I * (v (Fin.natAdd n i) : ℂ))) =
      (TauCeti.realCliffordForm (n + n) 0 v : ℂ)
  rw [TauCeti.realCliffordForm_zero_eq_weightedSumSquares_one]
  simp only [QuadraticMap.weightedSumSquares_apply, Pi.one_apply, one_smul, Fin.sum_univ_add]
  rw [← Finset.sum_add_distrib]
  simp only [Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (v (Fin.castAdd n i) : ℂ) ^ 2 - Complex.I ^ 2 *
        (v (Fin.natAdd n i) : ℂ) ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

def cliffordMap (n : ℕ) : CliffordAlgebra (realForm n) →ₐ[ℝ]
    CliffordAlgebra (complexForm n) :=
  CliffordAlgebra.lift (realForm n) ⟨
    ((CliffordAlgebra.ι (complexForm n)).restrictScalars ℝ).comp (coordinates n), by
      intro v
      rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, CliffordAlgebra.ι_sq_scalar,
        coordinates_form]
      exact IsScalarTower.algebraMap_apply ℝ ℂ _ _⟩

@[simp] theorem cliffordMap_ι (n : ℕ) (v : RealSpace n) :
    cliffordMap n (CliffordAlgebra.ι (realForm n) v) =
      CliffordAlgebra.ι (complexForm n) (coordinates n v) :=
  CliffordAlgebra.lift_ι_apply _ _ _

theorem cliffordMap_mem_even (n : ℕ) {x : CliffordAlgebra (realForm n)}
    (hx : x ∈ CliffordAlgebra.even (realForm n)) :
    cliffordMap n x ∈ CliffordAlgebra.even (complexForm n) := by
  change x ∈ CliffordAlgebra.evenOdd (realForm n) 0 at hx
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
    rw [(cliffordMap n).commutes, IsScalarTower.algebraMap_apply ℝ ℂ]
    exact (CliffordAlgebra.even (complexForm n)).algebraMap_mem _
  | add x y hx hy ihx ihy => exact map_add (cliffordMap n) x y ▸ add_mem ihx ihy
  | ι_mul_ι_mul v w x hx ih =>
    rw [map_mul, map_mul, cliffordMap_ι, cliffordMap_ι]
    exact mul_mem (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ _ _) ih

def evenMap (n : ℕ) : CliffordAlgebra.even (realForm n) →ₐ[ℝ]
    CliffordAlgebra.even (complexForm n) where
  toFun x := ⟨cliffordMap n x, cliffordMap_mem_even n x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  commutes' r := Subtype.ext ((cliffordMap n).commutes r)

end

end Math.CompactSpin.Polarized
