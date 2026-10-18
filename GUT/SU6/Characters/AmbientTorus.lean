import GUT.SU6.Characters.AmbientLaurent
import Math.LieGroups.Torus.CircleTorusCharacterLattice
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

open Math

/-!
# The compact maximal torus of SU(6)

This file realizes the abstract five-dimensional compact torus `Circle^5` as
the determinant-one diagonal subgroup of the concrete matrix group `SU(6)`.
The sixth coordinate is the inverse of the product of the first five.  The
construction is a continuous group homomorphism, is onto the diagonal points,
and pairs the integer character lattice with the canonical Laurent evaluator.
-/

open scoped BigOperators

namespace GUT
namespace AmbientTorus

open AmbientWeightLattice

noncomputable section

abbrev Torus := CircleTorusCharacterLattice.Torus I5
abbrev SU6 := ActualRestriction.SU6
abbrev DiagonalPoint := AmbientLaurent.DiagonalPoint

theorem diagonalPoint_ext {s t : DiagonalPoint}
    (h : s.coords = t.coords) : s = t := by
  cases s with
  | mk sCoords sMem =>
      cases t with
      | mk tCoords tMem =>
          dsimp at h
          subst tCoords
          rfl

/-- Six circle coordinates obtained from five independent coordinates by
imposing determinant one. -/
def circleCoords (x : Torus) : I6 → Circle :=
  Fin.snoc x (∏ i, x i)⁻¹

@[simp]
theorem circleCoords_castSucc (x : Torus) (i : I5) :
    circleCoords x i.castSucc = x i := by
  simp [circleCoords]

@[simp]
theorem circleCoords_last (x : Torus) :
    circleCoords x (Fin.last 5) = (∏ i, x i)⁻¹ := by
  exact Fin.snoc_last
    (α := fun _ : Fin 6 => Circle) (p := x) (x := (∏ i, x i)⁻¹)

@[simp]
theorem circleCoords_one : circleCoords (1 : Torus) = 1 := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp [circleCoords]
  · rw [circleCoords_last]
    simp

@[simp]
theorem circleCoords_mul (x y : Torus) :
    circleCoords (x * y) = circleCoords x * circleCoords y := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp [circleCoords]
  · change (∏ i, (x * y) i)⁻¹ =
      circleCoords x (Fin.last 5) * circleCoords y (Fin.last 5)
    rw [circleCoords_last, circleCoords_last]
    simp_rw [Pi.mul_apply]
    rw [Finset.prod_mul_distrib]
    simp [mul_comm]

/-- The same coordinates, coerced to complex numbers. -/
def coords (x : Torus) : I6 → ℂ :=
  fun i => (circleCoords x i : ℂ)

@[simp]
theorem coords_castSucc (x : Torus) (i : I5) :
    coords x i.castSucc = (x i : ℂ) := by
  simp [coords]

@[simp]
theorem coords_last (x : Torus) :
    coords x (Fin.last 5) = (((∏ i, x i)⁻¹ : Circle) : ℂ) := by
  simp only [coords, circleCoords_last]

@[simp]
theorem coords_one : coords (1 : Torus) = 1 := by
  funext i
  simp [coords]

@[simp]
theorem coords_mul (x y : Torus) :
    coords (x * y) = coords x * coords y := by
  funext i
  change ((circleCoords (x * y) i : Circle) : ℂ) =
    (circleCoords x i : ℂ) * (circleCoords y i : ℂ)
  rw [circleCoords_mul]
  rfl

theorem star_coords_mul (x : Torus) (i : I6) :
    star (coords x i) * coords x i = 1 := by
  change star ((circleCoords x i : Circle) : ℂ) *
      (circleCoords x i : ℂ) = 1
  rw [Complex.star_def, ← Circle.coe_inv_eq_conj]
  norm_cast
  simp

theorem diagonal_coords_mem_unitaryGroup (x : Torus) :
    Matrix.diagonal (coords x) ∈ Matrix.unitaryGroup I6 ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    have hi := star_coords_mul x i
    rw [mul_comm] at hi
    simpa [Matrix.one_apply] using hi
  · simp [h]

theorem determinant_coords (x : Torus) :
    (Matrix.diagonal (coords x) : Matrix I6 I6 ℂ).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_castSucc]
  change (∏ i : I5, (x i : ℂ)) * ((((∏ i : I5, x i)⁻¹ : Circle) : ℂ)) = 1
  have hProd :
      (∏ i : I5, (x i : ℂ)) = ((∏ i : I5, x i : Circle) : ℂ) := by
    change (∏ i : I5, Circle.coeHom (x i)) =
      Circle.coeHom (∏ i : I5, x i)
    exact (map_prod Circle.coeHom (fun i : I5 => x i) Finset.univ).symm
  rw [hProd]
  norm_cast
  simp

/-- A compact-torus point as an actual determinant-one diagonal matrix. -/
def diagonalPoint (x : Torus) : DiagonalPoint where
  coords := coords x
  mem := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    exact ⟨diagonal_coords_mem_unitaryGroup x, determinant_coords x⟩

/-- The concrete inclusion of the compact maximal torus into `SU(6)`. -/
def toSU6MonoidHom : Torus →* SU6 where
  toFun := fun x => (diagonalPoint x).toSU6
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal (coords 1) = 1
    rw [coords_one]
    ext i j
    change (if i = j then 1 else 0) = (if i = j then 1 else 0)
    rfl
  map_mul' := by
    intro x y
    apply Subtype.ext
    change Matrix.diagonal (coords (x * y)) =
      Matrix.diagonal (coords x) * Matrix.diagonal (coords y)
    rw [Matrix.diagonal_mul_diagonal, coords_mul]
    rfl

theorem continuous_circleCoords_apply (i : I6) :
    Continuous fun x : Torus => circleCoords x i := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simpa using (continuous_apply j : Continuous fun x : Torus => x j)
  · simp only [circleCoords_last]
    fun_prop

theorem continuous_coords_apply (i : I6) :
    Continuous fun x : Torus => coords x i := by
  exact continuous_subtype_val.comp (continuous_circleCoords_apply i)

theorem continuous_toSU6MonoidHom :
    Continuous toSU6MonoidHom := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous fun x : Torus => Matrix.diagonal (coords x) i j
  by_cases h : i = j
  · subst j
    simpa using continuous_coords_apply i
  · simpa [Matrix.diagonal_apply_ne _ h] using
      (continuous_const : Continuous fun _ : Torus => (0 : ℂ))

/-- The compact maximal-torus inclusion as a continuous monoid homomorphism. -/
def toSU6 : Torus →ₜ* SU6 where
  toMonoidHom := toSU6MonoidHom
  continuous_toFun := continuous_toSU6MonoidHom

/-- Recover the five independent circle coordinates of a diagonal point. -/
def ofDiagonalPoint (t : DiagonalPoint) : Torus :=
  fun i => ⟨t.coords i.castSucc, by
    simp only [Submonoid.unitSphere]
    exact mem_sphere_zero_iff_norm.2 (t.norm_coord i.castSucc)⟩

@[simp]
theorem ofDiagonalPoint_apply_coe (t : DiagonalPoint) (i : I5) :
    ((ofDiagonalPoint t i : Circle) : ℂ) = t.coords i.castSucc :=
  rfl

theorem diagonalPoint_ofDiagonalPoint (t : DiagonalPoint) :
    diagonalPoint (ofDiagonalPoint t) = t := by
  have hCoords : coords (ofDiagonalPoint t) = t.coords := by
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp only [coords, circleCoords_castSucc,
        ofDiagonalPoint_apply_coe]
    · have hDet := t.det_product
      rw [Fin.prod_univ_castSucc] at hDet
      change (((∏ j : I5, ofDiagonalPoint t j)⁻¹ : Circle) : ℂ) =
        t.coords (Fin.last 5)
      rw [Circle.coe_inv]
      have hProd : ((∏ j : I5, ofDiagonalPoint t j : Circle) : ℂ) =
          ∏ j : I5, t.coords j.castSucc := by
        change Circle.coeHom (∏ j : I5, ofDiagonalPoint t j) =
          ∏ j : I5, t.coords j.castSucc
        rw [map_prod]
        apply Finset.prod_congr rfl
        intro j _hj
        exact ofDiagonalPoint_apply_coe t j
      rw [hProd]
      exact inv_eq_of_mul_eq_one_right hDet
  exact diagonalPoint_ext hCoords

theorem toTorusVec_diagonalPoint (x : Torus) :
    (diagonalPoint x).toTorusVec = fun i => Circle.toUnits (x i) := by
  funext i
  apply Units.ext
  simp [diagonalPoint, AmbientLaurent.DiagonalPoint.toTorusVec,
    AmbientLaurent.DiagonalPoint.coordUnit]

/-- Integer compact-torus characters and normalized Laurent monomials have
exactly the same complex evaluation. -/
theorem exponent_eval_diagonalPoint
    (weight : Exponent) (x : Torus) :
    AmbientLaurent.Exponent.eval weight (diagonalPoint x).toTorusVec =
      ((CircleTorusCharacterLattice.torusCharacter weight x : Circle) : ℂ) := by
  rw [toTorusVec_diagonalPoint]
  simp only [AmbientLaurent.Exponent.eval, AmbientLaurent.Exponent.evalUnit,
    CircleTorusCharacterLattice.torusCharacter_apply]
  change Units.coeHom ℂ (∏ i : I5, Circle.toUnits (x i) ^ weight i) =
    Circle.coeHom (∏ i : I5, x i ^ weight i)
  rw [map_prod, map_prod]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [map_zpow, map_zpow]
  change ((x i : Circle) : ℂ) ^ weight i =
    ((x i : Circle) : ℂ) ^ weight i
  rfl

end
end AmbientTorus
end GUT
