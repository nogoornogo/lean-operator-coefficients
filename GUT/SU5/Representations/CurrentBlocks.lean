import GUT.SU5.Branching.ExteriorSquare
import GUT.SU6.Embeddings.SpecialUnitaryLieAlgebra
import Math.RepresentationTheory.Exterior.ExteriorSquareCoordinates
import Mathlib.Analysis.Calculus.Deriv.Prod

open Physics

open Math

/-! A pilot on the actual ten: the same compact SU(5) direction has nonzero
electron-left to quark and quark to up-left first-order coefficients. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GUT.SU5.CurrentBlocks
noncomputable section

open SpecialUnitaryLieAlgebra ExteriorSquareCoordinates
open scoped Matrix Matrix.Norms.L2Operator TensorProduct

def directionMatrix : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.single 0 3 1 - Matrix.single 3 0 1

def direction : CompactRealForm (Fin 5) where
  toSpecialLinear := ⟨directionMatrix, by
    change Matrix.trace directionMatrix = 0
    norm_num [directionMatrix, Matrix.trace, Fin.sum_univ_succ, Matrix.single_apply]⟩
  skewAdjoint := by
    change directionMatrixᴴ = -directionMatrix
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [directionMatrix, Matrix.conjTranspose_apply, Matrix.single_apply]

def curve (t : ℝ) : StandardModelEmbedding.TargetGroup :=
  CompactRealForm.expSpecialUnitary (t • direction)

def electron : Pair 5 := ⟨(3, 4), by decide⟩
def quarkOut : Pair 5 := ⟨(0, 4), by decide⟩
def quarkIn : Pair 5 := ⟨(1, 3), by decide⟩
def up : Pair 5 := ⟨(0, 1), by decide⟩

def coefficient (a b : Pair 5) (g : StandardModelEmbedding.TargetGroup) : ℂ :=
  (basis (n := 5)).repr (Matter.ten g (basis b)) a

theorem coefficient_eq_matrix (a b : Pair 5) (g : StandardModelEmbedding.TargetGroup) :
    coefficient a b g = matrix g.val a b := by
  rw [matrix, LinearMap.toMatrix_apply]
  rfl

theorem curve_entry_hasDerivAt (i j : Fin 5) :
    HasDerivAt (fun t => (curve t).val i j) (directionMatrix i j) 0 := by
  have h : HasDerivAt (fun t : ℝ => (curve t).val) directionMatrix 0 := by
    let hNormed : NormedAddCommGroup (Matrix (Fin 5) (Fin 5) ℂ) :=
      NonUnitalNormedRing.toNormedAddCommGroup
    let : AddCommGroup (Matrix (Fin 5) (Fin 5) ℂ) := hNormed.toAddCommGroup
    change HasDerivAt (fun t : ℝ => NormedSpace.exp (t • directionMatrix)) _ 0
    simpa using hasDerivAt_exp_smul_const directionMatrix (0 : ℝ)
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp h i) j

theorem coefficient_hasDerivAt (a b : Pair 5) :
    HasDerivAt (fun t => coefficient a b (curve t)) (tangent directionMatrix a b) 0 := by
  simp_rw [coefficient_eq_matrix]
  apply hasDerivAt_matrix curve_entry_hasDerivAt
  simp [curve]

theorem electron_quark_derivative :
    HasDerivAt (fun t => coefficient quarkOut electron (curve t)) 1 0 := by
  simpa [tangent, directionMatrix, quarkOut, electron] using
    coefficient_hasDerivAt quarkOut electron

theorem quark_up_derivative :
    HasDerivAt (fun t => coefficient up quarkIn (curve t)) (-1) 0 := by
  simpa [tangent, directionMatrix, up, quarkIn] using
    coefficient_hasDerivAt up quarkIn

open SMEpsilonTensor ExteriorSquareBranching

private theorem split_color (i : Fin 3) :
    FundamentalBranching.splitEquiv (Pi.single (Fin.castAdd 2 i) 1) =
      (Pi.single i 1, 0) := by
  apply Prod.ext <;> ext j <;> fin_cases i <;> fin_cases j <;>
    norm_num [FundamentalBranching.splitEquiv, Pi.single_apply, Fin.ext_iff]

private theorem split_weak (i : Fin 2) :
    FundamentalBranching.splitEquiv (Pi.single (Fin.natAdd 3 i) 1) =
      (0, Pi.single i 1) := by
  apply Prod.ext <;> ext j <;> fin_cases i <;> fin_cases j <;>
    norm_num [FundamentalBranching.splitEquiv, Pi.single_apply, Fin.ext_iff]

theorem electron_species :
    branch (basis electron) = (0, (0, (LinearMap.id : ℂ →ₗ[ℂ] ℂ))) := by
  rw [basis_apply, branch_wedge]
  change pair (FundamentalBranching.splitEquiv (Pi.single (Fin.natAdd 3 (0 : Fin 2)) 1))
    (FundamentalBranching.splitEquiv (Pi.single (Fin.natAdd 3 (1 : Fin 2)) 1)) = _
  rw [split_weak, split_weak, pair_weak_weak]
  norm_num [eps2, Pi.single_apply]

theorem quarkOut_species :
    branch (basis quarkOut) =
      (0, ((Pi.single (0 : Fin 3) 1) ⊗ₜ[ℂ] (Pi.single (1 : Fin 2) 1), 0)) := by
  rw [basis_apply, branch_wedge]
  change pair (FundamentalBranching.splitEquiv (Pi.single (Fin.castAdd 2 (0 : Fin 3)) 1))
    (FundamentalBranching.splitEquiv (Pi.single (Fin.natAdd 3 (1 : Fin 2)) 1)) = _
  rw [split_color, split_weak, pair_color_weak]

theorem quarkIn_species :
    branch (basis quarkIn) =
      (0, ((Pi.single (1 : Fin 3) 1) ⊗ₜ[ℂ] (Pi.single (0 : Fin 2) 1), 0)) := by
  rw [basis_apply, branch_wedge]
  change pair (FundamentalBranching.splitEquiv (Pi.single (Fin.castAdd 2 (1 : Fin 3)) 1))
    (FundamentalBranching.splitEquiv (Pi.single (Fin.natAdd 3 (0 : Fin 2)) 1)) = _
  rw [split_color, split_weak, pair_color_weak]

theorem up_species :
    branch (basis up) = ((LinearMap.proj (2 : Fin 3)), (0, 0)) := by
  rw [basis_apply, branch_wedge]
  change pair (FundamentalBranching.splitEquiv (Pi.single (Fin.castAdd 2 (0 : Fin 3)) 1))
    (FundamentalBranching.splitEquiv (Pi.single (Fin.castAdd 2 (1 : Fin 3)) 1)) = _
  rw [split_color, split_color, pair_color_color]
  apply Prod.ext
  · apply LinearMap.ext
    intro c
    change eps3 (Pi.single 0 1) (Pi.single 1 1) c = c 2
    norm_num [eps3, Pi.single_apply, Fin.ext_iff]
  · rfl

def quarkProbe : StandardSMGaugeTensor.Quark →ₗ[ℂ] ℂ :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun (a : Color) (b : Weak) => a 0 * b 1)
    (by intros; simp [add_mul]) (by intros; simp [mul_assoc])
    (by intros; simp [mul_add]) (by intros; simp [mul_left_comm]))

def quarkCoordinate : Matter.Ten →ₗ[ℂ] ℂ :=
  quarkProbe.comp ((LinearMap.fst ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp branch))

def upCoordinate : Matter.Ten →ₗ[ℂ] ℂ where
  toFun v := (branch v).1 (Pi.single 2 1)
  map_add' v w := by simp
  map_smul' z v := by simp

theorem quarkCoordinate_eq : quarkCoordinate = (basis (n := 5)).coord quarkOut := by
  apply (basis (n := 5)).ext
  intro p
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  fin_cases p <;>
    norm_num [quarkCoordinate, quarkProbe, basis_apply, branch_wedge, pair,
      FundamentalBranching.splitEquiv, eps2, Pi.single_apply,
      quarkOut, Finsupp.single_apply, Subtype.ext_iff, Fin.ext_iff]

private theorem eps3Trilin_apply (a b c : Color) : eps3Trilin a b c = eps3 a b c := rfl

theorem upCoordinate_eq : upCoordinate = (basis (n := 5)).coord up := by
  apply (basis (n := 5)).ext
  intro p
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  fin_cases p <;>
    norm_num [upCoordinate, basis_apply, branch_wedge, pair,
      FundamentalBranching.splitEquiv, eps3Trilin_apply, eps3, Pi.single_apply,
      up, Finsupp.single_apply, Subtype.ext_iff, Fin.ext_iff]

theorem species_derivatives :
    HasDerivAt (fun t => quarkCoordinate (Matter.ten (curve t) (basis electron))) 1 0 ∧
    HasDerivAt (fun t => upCoordinate (Matter.ten (curve t) (basis quarkIn))) (-1) 0 := by
  rw [quarkCoordinate_eq, upCoordinate_eq]
  exact ⟨electron_quark_derivative, quark_up_derivative⟩

theorem both_blocks_nonzero :
    deriv (fun t => quarkCoordinate (Matter.ten (curve t) (basis electron))) 0 ≠ 0 ∧
    deriv (fun t => upCoordinate (Matter.ten (curve t) (basis quarkIn))) 0 ≠ 0 := by
  rw [species_derivatives.1.deriv, species_derivatives.2.deriv]
  norm_num

/-- Both channels depend on the same fundamental matrix entry. -/
theorem cross_block_formula (X : Matrix (Fin 5) (Fin 5) ℂ) :
    tangent X quarkOut electron = X 0 3 ∧
    tangent X up quarkIn = -X 0 3 := by
  simp [tangent, quarkOut, electron, up, quarkIn]

theorem selected_tangents_zero_of_entry_zero
    (X : Matrix (Fin 5) (Fin 5) ℂ) (h : X 0 3 = 0) :
    tangent X quarkOut electron = 0 ∧ tangent X up quarkIn = 0 := by
  rw [(cross_block_formula X).1, (cross_block_formula X).2, h, neg_zero]
  exact ⟨rfl, rfl⟩

theorem coefficients_at_zero :
    coefficient quarkOut electron (curve 0) = 0 ∧
    coefficient up quarkIn (curve 0) = 0 := by
  simp [curve, coefficient, quarkOut, electron, up, quarkIn]

end
end GUT.SU5.CurrentBlocks
