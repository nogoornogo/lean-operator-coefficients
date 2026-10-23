import Math.Algebra.Jets.MatrixJetConnection
import Math.RepresentationTheory.Jets.NonlinearJetIBP

/-! Source-free formal matrix Yang–Mills equations. Connection components
are actual ordinary polynomial jets. No local gauge classification is assumed. -/
namespace Physics.FormalYangMills
set_option autoImplicit false
noncomputable section
open Math Math.FormalConnection MvPolynomial

variable (N : Type*) [Fintype N] [DecidableEq N]

abbrev Components := Fin 4 × N × N
abbrev OffShell := ScalarJetAlgebra.Algebra (Components N) (Fin 4)
abbrev Mat := Matrix N N (OffShell N)
abbrev D := ScalarJetAlgebra.totalDerivative (S := Components N) (I := Fin 4)
abbrev ordinary : Ordinary (Fin 4) (Mat N) := matrixOrdinary

def connection (i : Fin 4) : Mat N := fun a b => X ((i, a, b), 0)
def F (i j : Fin 4) : Mat N := curvature (ordinary N) (connection N) i j
def nabla (i : Fin 4) : Mat N →ₗ[ℂ] Mat N := covariant (ordinary N) (connection N) i
def sign (i : Fin 4) : ℂ := if i = 0 then 1 else -1
def equation (j : Fin 4) : Mat N := ∑ i, sign i • nabla N i (F N i j)
def equations : Set (OffShell N) := Set.range (fun j : Components N => equation N j.1 j.2.1 j.2.2)
abbrev ideal := DifferentialEquation.ideal (D N) (equations N)
abbrev Shell := DifferentialEquation.Shell (D N) (equations N)
abbrev projection := DifferentialEquation.projection (D N) (equations N)

theorem curvature_antisymmetric (i j : Fin 4) : F N i j = -F N j i :=
  curvature_skew _ _ _ _

theorem commutator (i j : Fin 4) (x : Mat N) :
    nabla N i (nabla N j x) - nabla N j (nabla N i x) = bracket (F N i j) x :=
  covariant_commutator _ _ _ _ _

theorem bianchi (i j k : Fin 4) :
    nabla N i (F N j k) + nabla N j (F N k i) + nabla N k (F N i j) = 0 :=
  FormalConnection.bianchi _ _ _ _ _

theorem equation_mem (j : Fin 4) (a b : N) : equation N j a b ∈ ideal N :=
  DifferentialEquation.seed_mem _ _ ⟨(j, a, b), rfl⟩

theorem descendants_zero (w : List (Fin 4)) (j : Fin 4) (a b : N) :
    projection N (DifferentialEquation.word (D N) w (equation N j a b)) = 0 :=
  (DifferentialEquation.projection_eq_zero _ _ _).mpr
    (DifferentialEquation.descendant_mem _ _ w ⟨(j, a, b), rfl⟩)

def entriesMem (x : Mat N) : Prop := ∀ a b, x a b ∈ ideal N

theorem entries_mul_left (x y : Mat N) (hy : entriesMem N y) : entriesMem N (x * y) := by
  intro a b
  rw [Matrix.mul_apply]
  exact (ideal N).sum_mem (fun k _ => (ideal N).mul_mem_left _ (hy k b))

theorem entries_mul_right (x y : Mat N) (hx : entriesMem N x) : entriesMem N (x * y) := by
  intro a b
  rw [Matrix.mul_apply]
  exact (ideal N).sum_mem (fun k _ => (ideal N).mul_mem_right _ (hx a k))

theorem entries_nabla (i : Fin 4) (x : Mat N) (hx : entriesMem N x) : entriesMem N (nabla N i x) := by
  intro a b
  change D N i (x a b) + ((connection N i * x) a b - (x * connection N i) a b) ∈ ideal N
  exact (ideal N).add_mem (DifferentialEquation.stable _ _ i (hx a b))
    ((ideal N).sub_mem (entries_mul_left N _ _ hx a b) (entries_mul_right N _ _ hx a b))

def covariantWord : List (Fin 4) → Mat N → Mat N
  | [], x => x
  | i :: w, x => nabla N i (covariantWord w x)

theorem covariant_descendants_mem (w : List (Fin 4)) (j : Fin 4) :
    entriesMem N (covariantWord N w (equation N j)) := by
  induction w with
  | nil => exact equation_mem N j
  | cons i w ih => exact entries_nabla N i _ ih

theorem covariant_descendants_zero (w : List (Fin 4)) (j : Fin 4) (a b : N) :
    projection N (covariantWord N w (equation N j) a b) = 0 :=
  (DifferentialEquation.projection_eq_zero _ _ _).mpr (covariant_descendants_mem N w j a b)

omit [Fintype N] [DecidableEq N] in
theorem zeroEvaluation_connection (i : Fin 4) (a b : N) :
    ScalarJetAlgebra.zeroEvaluation (connection N i a b) = 0 := by
  exact ScalarJetAlgebra.zeroEvaluation_X _

theorem zeroEvaluation_F (i j : Fin 4) (a b : N) :
    ScalarJetAlgebra.zeroEvaluation (F N i j a b) = 0 := by
  change ScalarJetAlgebra.zeroEvaluation
    (D N i (connection N j a b) - D N j (connection N i a b) +
      ((connection N i * connection N j) a b - (connection N j * connection N i) a b)) = 0
  simp [Matrix.mul_apply, zeroEvaluation_connection, ScalarJetAlgebra.zeroEvaluation_derivative]

theorem zeroEvaluation_equation (j : Fin 4) (a b : N) :
    ScalarJetAlgebra.zeroEvaluation (equation N j a b) = 0 := by
  simp only [equation, Matrix.sum_apply, Matrix.smul_apply, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro i hi
  change sign i • ScalarJetAlgebra.zeroEvaluation
    (D N i (F N i j a b) + ((connection N i * F N i j) a b - (F N i j * connection N i) a b)) = 0
  simp [Matrix.mul_apply, zeroEvaluation_connection, ScalarJetAlgebra.zeroEvaluation_derivative]

theorem unit_survives : projection N 1 ≠ 0 := by
  rw [ne_eq, DifferentialEquation.projection_eq_zero]
  apply DifferentialEquation.one_not_mem _ _ ScalarJetAlgebra.zeroEvaluation
  · rintro p ⟨j, rfl⟩
    exact zeroEvaluation_equation N _ _ _
  · exact ScalarJetAlgebra.zeroEvaluation_derivative

def sourceEquiv := DifferentialEquation.sourceEquiv (D N) (equations N)
def coefficientEquiv := DifferentialEquation.coefficientEquiv (W := ℂ) (D N) (equations N)

theorem projection_kernel : RingHom.ker (projection N).toRingHom = ideal N :=
  DifferentialEquation.projection_kernel _ _

theorem projection_surjective : Function.Surjective (projection N) :=
  DifferentialEquation.projection_surjective _ _

def finiteImage (n d : ℕ) := DifferentialEquation.image (D N) (equations N)
  (ScalarJetAlgebra.grade (S := Components N) (I := Fin 4) n d)

instance finiteImage_finite (n d : ℕ) : FiniteDimensional ℂ (finiteImage N n d) := by
  unfold finiteImage
  infer_instance

end
end Physics.FormalYangMills
