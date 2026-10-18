import GUT.SU6.SelectionRules.StandardBranch.StandardPhysicalSource
import GUT.SU6.Branching.StandardU5Group

/-!
# The common central circle in the standard U(5) branch

This file constructs the actual group homomorphism

`Circle -> SU(6), z |-> diag(z,z,z,z,z,z^(-5))`

through the checked standard `U(5)` embedding.  It then proves directly that
an ambient Laurent monomial restricts to this circle with exponent equal to
its `U(5)` total degree.  This is the concrete gauge-side counterpart of the
`centralCharge totalDegree` term in the standard charge-orbit bridge affine charge model.
-/

open scoped BigOperators

namespace GUT
namespace StandardCentralGauge

noncomputable section

abbrev U5 := StandardU5Group.U5
abbrev SU6 := ActualRestriction.SU6
abbrev Exponent := AmbientWeightLattice.Exponent

/-- A scalar unitary matrix in the defining five-dimensional block. -/
def scalarMatrix (z : Circle) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal fun _ => (z : ℂ)

theorem scalarMatrix_mem_unitary (z : Circle) :
    scalarMatrix z ∈ Matrix.unitaryGroup (Fin 5) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [scalarMatrix, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [← Circle.coe_inv_eq_conj]
  · simp [hij]

def scalarU5 (z : Circle) : U5 :=
  ⟨scalarMatrix z, scalarMatrix_mem_unitary z⟩

@[simp]
theorem scalarU5_one : scalarU5 1 = 1 := by
  apply Subtype.ext
  ext i j
  simp [scalarU5, scalarMatrix]

@[simp]
theorem scalarU5_mul (z w : Circle) :
    scalarU5 (z * w) = scalarU5 z * scalarU5 w := by
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst j
    simp [scalarU5, scalarMatrix]
  · simp [scalarU5, scalarMatrix, hij]

/-- The common scalar circle inside the checked standard `U(5)` subgroup. -/
def scalarU5Hom : Circle →* U5 where
  toFun := scalarU5
  map_one' := scalarU5_one
  map_mul' := scalarU5_mul

/-- The corresponding concrete gauge circle in `SU(6)`. -/
def hom : Circle →* SU6 :=
  StandardU5Group.embedding.comp scalarU5Hom

/-- The rank-five torus point seen by the normalized Laurent evaluator. -/
def torusVec (z : Circle) : AmbientLaurent.TorusVec :=
  fun _ => Circle.toUnits z

theorem prod_zpow_eq_zpow_sum
    {G : Type*} [CommGroup G] (a : G) (e : Fin 5 → ℤ) :
    ∏ i, a ^ e i = a ^ ∑ i, e i := by
  classical
  induction (Finset.univ : Finset (Fin 5)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add, ih]

/-- Restricting a Laurent monomial to the common scalar circle reads exactly
its total `U(5)` degree. -/
theorem exponent_eval_torusVec
    (e : Exponent) (z : Circle) :
    AmbientLaurent.Exponent.eval e (torusVec z) =
      ((z ^ StandardAbelianCharge.totalDegree e : Circle) : ℂ) := by
  change
    ((∏ i, Circle.toUnits z ^ e i : ℂˣ) : ℂ) =
      ((z ^ ∑ i, e i : Circle) : ℂ)
  rw [prod_zpow_eq_zpow_sum]
  rw [← map_zpow]
  simp [Circle.toUnits_apply]

/-- The explicit six diagonal coordinates of the same gauge circle. -/
def coords (z : Circle) : Fin 6 → ℂ :=
  ![(z : ℂ), (z : ℂ), (z : ℂ), (z : ℂ), (z : ℂ),
    ((z ^ (-5 : ℤ) : Circle) : ℂ)]

theorem coords_continuous : Continuous coords := by
  have hCoe : Continuous fun z : Circle => (z : ℂ) :=
    (isometry_subtype_coe : Isometry ((↑) : Circle → ℂ)).continuous
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [coords] using hCoe
  · simpa [coords] using hCoe
  · simpa [coords] using hCoe
  · simpa [coords] using hCoe
  · simpa [coords] using hCoe
  · change Continuous fun z : Circle => ((z ^ (-5 : ℤ) : Circle) : ℂ)
    exact (hCoe.comp
      (continuous_zpow (-5 : ℤ) :
        Continuous fun z : Circle => z ^ (-5 : ℤ))).congr fun _ => rfl

theorem diagonal_coords_mem_unitary (z : Circle) :
    Matrix.diagonal (coords z) ∈ Matrix.unitaryGroup (Fin 6) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    fin_cases i <;>
      simp [coords, ← Circle.coe_inv_eq_conj]
  · simp [hij]

theorem diagonal_coords_det (z : Circle) :
    Matrix.det (Matrix.diagonal (coords z)) = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_six]
  have hz : z * z * z * z * z * z ^ (-5 : ℤ) = 1 := by
    calc
      z * z * z * z * z * z ^ (-5 : ℤ) =
          z ^ (5 : ℕ) * z ^ (-5 : ℤ) := by group
      _ = 1 := by rw [← zpow_natCast]; simp
  exact congrArg (fun w : Circle => (w : ℂ)) hz

/-- The concrete diagonal point corresponding to the common scalar circle. -/
def diagonalPoint (z : Circle) : AmbientLaurent.DiagonalPoint where
  coords := coords z
  mem := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    exact ⟨diagonal_coords_mem_unitary z, diagonal_coords_det z⟩

@[simp]
theorem diagonalPoint_toTorusVec (z : Circle) :
    (diagonalPoint z).toTorusVec = torusVec z := by
  funext i
  fin_cases i <;>
    apply Units.ext <;>
    rfl

theorem torusPoint_diagonalPoint (z : Circle) :
    StandardU5Group.torusPoint (diagonalPoint z) = scalarU5 z := by
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst j
    fin_cases i <;>
      simp [StandardU5Group.torusPoint, StandardU5Group.torusMatrix,
        diagonalPoint, coords, scalarU5, scalarMatrix]
  · simp [StandardU5Group.torusPoint, StandardU5Group.torusMatrix,
      diagonalPoint, coords, scalarU5, scalarMatrix, hij]

/-- The diagonal realization agrees with the homomorphism constructed through
the standard `U(5)` embedding. -/
theorem diagonalPoint_toSU6_eq_hom (z : Circle) :
    (diagonalPoint z).toSU6 = hom z := by
  calc
    (diagonalPoint z).toSU6 =
        StandardU5Group.embedding
          (StandardU5Group.torusPoint (diagonalPoint z)) :=
      (StandardU5Group.embedding_torusPoint (diagonalPoint z)).symm
    _ = StandardU5Group.embedding (scalarU5 z) := by
      rw [torusPoint_diagonalPoint]
    _ = hom z := rfl

/-- The concrete standard central circle is continuous in the ambient matrix
topology. -/
theorem hom_continuous : Continuous hom := by
  apply continuous_induced_rng.mpr
  have hDiagonal : Continuous fun z : Circle => Matrix.diagonal (coords z) :=
    coords_continuous.matrix_diagonal
  apply hDiagonal.congr
  intro z
  exact congrArg Subtype.val (diagonalPoint_toSU6_eq_hom z)

/-- Bundled continuous version of the standard central gauge circle. -/
def continuousHom : Circle →ₜ* SU6 where
  toMonoidHom := hom
  continuous_toFun := hom_continuous

/-- Polynomial evaluation on the actual central gauge point is evaluation at
the constant rank-five torus vector. -/
theorem diagonalEval_diagonalPoint
    (p : AmbientLaurent.Poly) (z : Circle) :
    AmbientLaurent.diagonalEval p (diagonalPoint z) =
      AmbientLaurent.eval p (torusVec z) := by
  rw [AmbientLaurent.diagonalEval, diagonalPoint_toTorusVec]

end
end StandardCentralGauge
end GUT
