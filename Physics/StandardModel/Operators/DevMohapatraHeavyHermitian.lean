import Physics.StandardModel.Operators.DevMohapatraHeavyAction
import Physics.StandardModel.Operators.DevMohapatraHeavyProjection
import Math.LinearAlgebra.ExteriorHermitianConjugation

/-! The concrete complex-conjugating field dictionary on the doubled
Grassmann carrier. No independently supplied barred-action convention. -/
namespace GUT.DevMohapatraHeavyHermitian
set_option autoImplicit false
noncomputable section
open DevMohapatraHeavyElimination DevMohapatraHeavyAction DevMohapatraTreeLevel
open Math.ExteriorHermitianConjugation

def swapExternal (i : Fin 36) : Fin 36 :=
  if h : i.val < 18 then ⟨i.val+18, by omega⟩ else ⟨i.val-18, by omega⟩
def swapHeavy (i : Fin 4) : Fin 4 :=
  if h : i.val < 2 then ⟨i.val+2, by omega⟩ else ⟨i.val-2, by omega⟩

theorem swapExternal_involutive (i : Fin 36) : swapExternal (swapExternal i) = i := by
  fin_cases i <;> rfl

theorem swapHeavy_involutive (i : Fin 4) : swapHeavy (swapHeavy i) = i := by
  fin_cases i <;> rfl

def fieldConjugation : V →ₛₗ[starRingEnd ℂ] V := coordinateConjugation swapExternal
def heavyConjugation : (Fin 4 → ℂ) →ₛₗ[starRingEnd ℂ] (Fin 4 → ℂ) :=
  coordinateConjugation swapHeavy

def conjugation : W →ₛₗ[starRingEnd ℂ] W where
  toFun w := (fieldConjugation w.1, heavyConjugation w.2)
  map_add' x y := by simp
  map_smul' z x := by simp

theorem conjugation_involutive (w : W) : conjugation (conjugation w) = w := by
  exact Prod.ext
    (coordinateConjugation_involutive swapExternal swapExternal_involutive w.1)
    (coordinateConjugation_involutive swapHeavy swapHeavy_involutive w.2)

def hc (x : B) : B := adjoint conjugation x

theorem hc_mul (x y : B) : hc (x*y) = hc y*hc x := adjoint_mul conjugation x y
theorem hc_smul (z : ℂ) (x : B) : hc (z • x) = star z • hc x := adjoint_smul conjugation z x
theorem hc_add (x y : B) : hc (x+y) = hc x+hc y := by simp [hc, adjoint]
theorem hc_sub (x y : B) : hc (x-y) = hc x-hc y := by simp [hc, adjoint]
theorem hc_involutive (x : B) : hc (hc x) = x := adjoint_involutive _ conjugation_involutive x

theorem fieldConjugation_u (c : Fin 3) (r : Fin 2) : fieldConjugation (u c r) = ub c r := by
  rw [fieldConjugation, u, coord, coordinateConjugation_basis _ swapExternal_involutive]
  congr 1
  apply Fin.ext
  simp [swapExternal, show 2*c.val+r.val < 18 from by omega]
  omega

theorem fieldConjugation_d (c : Fin 3) (r : Fin 2) : fieldConjugation (d c r) = db c r := by
  rw [fieldConjugation, d, coord, coordinateConjugation_basis _ swapExternal_involutive]
  congr 1
  apply Fin.ext
  simp [swapExternal, show 6+2*c.val+r.val < 18 from by omega]
  omega

theorem fieldConjugation_s (c : Fin 3) (r : Fin 2) : fieldConjugation (s c r) = sb c r := by
  rw [fieldConjugation, s, coord, coordinateConjugation_basis _ swapExternal_involutive]
  congr 1
  apply Fin.ext
  simp [swapExternal, show 12+2*c.val+r.val < 18 from by omega]
  omega

theorem hc_heavy (i : Fin 4) : hc (heavy i) = heavy (swapHeavy i) := by
  simp only [hc, adjoint, heavy, conjugate_generator, CliffordAlgebra.reverse_ι]
  congr 1
  change (fieldConjugation 0, heavyConjugation (Pi.basisFun ℂ (Fin 4) i)) =
    (0, Pi.basisFun ℂ (Fin 4) (swapHeavy i))
  exact Prod.ext (map_zero _) (coordinateConjugation_basis _ swapHeavy_involutive i)

theorem hc_external_generator (v : V) :
    hc (includeExternal (ExteriorAlgebra.ι ℂ v)) =
      includeExternal (ExteriorAlgebra.ι ℂ (fieldConjugation v)) := by
  simp [hc, adjoint, includeExternal, ExteriorAlgebra.map_apply_ι, conjugation]

theorem hc_generator (v : W) : hc (ExteriorAlgebra.ι ℂ v) = ExteriorAlgebra.ι ℂ (conjugation v) := by
  simp [hc, adjoint]

theorem hc_pair (x y : Fin 2 → W) :
    hc (pair x y) = -pair (fun i => conjugation (x i)) (fun i => conjugation (y i)) := by
  calc
    _ = -pair (fun i => conjugation (y i)) (fun i => conjugation (x i)) := by
      simp [pair, hc_sub, hc_mul, hc_generator]
    _ = _ := by rw [pair_symmetric]

theorem hc_sum {I : Type*} (t : Finset I) (f : I → B) :
    hc (∑ i ∈ t, f i) = ∑ i ∈ t, hc (f i) := by simp [hc, adjoint, map_sum]

theorem epsilon_real (a b c : Fin 3) :
    star (SMEpsilonTensor.eps3 (SMEpsilonTensor.colorBasis a)
      (SMEpsilonTensor.colorBasis b) (SMEpsilonTensor.colorBasis c)) =
      SMEpsilonTensor.eps3 (SMEpsilonTensor.colorBasis a)
        (SMEpsilonTensor.colorBasis b) (SMEpsilonTensor.colorBasis c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [SMEpsilonTensor.eps3, SMEpsilonTensor.colorBasis, Pi.single_apply]

theorem hc_down (x y : Fin 3 → Fin 2 → W) (a : Fin 3) :
    hc (downCurrent x y a) =
      -downCurrent (fun c r => conjugation (x c r)) (fun c r => conjugation (y c r)) a := by
  simp only [downCurrent, hc_sum, hc_smul, hc_pair, epsilon_real, smul_neg,
    Finset.sum_neg_distrib]

def uw (c : Fin 3) (r : Fin 2) : W := (u c r, 0)
def dw (c : Fin 3) (r : Fin 2) : W := (d c r, 0)
def sw (c : Fin 3) (r : Fin 2) : W := (s c r, 0)
def ubw (c : Fin 3) (r : Fin 2) : W := (ub c r, 0)
def dbw (c : Fin 3) (r : Fin 2) : W := (db c r, 0)
def sbw (c : Fin 3) (r : Fin 2) : W := (sb c r, 0)

theorem conjugation_fields (c : Fin 3) (r : Fin 2) :
    conjugation (uw c r) = ubw c r ∧ conjugation (dw c r) = dbw c r ∧
      conjugation (sw c r) = sbw c r := by
  simp [conjugation, uw, dw, sw, ubw, dbw, sbw,
    fieldConjugation_u, fieldConjugation_d, fieldConjugation_s]

theorem include_down (x y : Fin 3 → Fin 2 → V) (a : Fin 3) :
    includeExternal (downCurrent x y a) =
      downCurrent (fun c r => (x c r, 0)) (fun c r => (y c r, 0)) a := by
  simp [includeExternal, downCurrent, pair, ExteriorAlgebra.map_apply_ι]

theorem include_current (x y z : Fin 3 → Fin 2 → V) (r : Fin 2) :
    includeExternal (current x y z r) =
      current (fun c r => (x c r, 0)) (fun c r => (y c r, 0)) (fun c r => (z c r, 0)) r := by
  simp [includeExternal, current, term, cubic_apply, ExteriorAlgebra.map_apply_ι]

def U (c : Fin 3) : B := pair ![heavyVector 0, heavyVector 1] (uw c)
def Ub (c : Fin 3) : B := pair ![heavyVector 2, heavyVector 3] (ubw c)
def D (c : Fin 3) : B := includeExternal (downCurrent d s c)
def Db (c : Fin 3) : B := includeExternal (downCurrent db sb c)

theorem hc_U (c : Fin 3) : hc (U c) = -Ub c := by
  rw [U, hc_pair]
  have hn (i : Fin 2) : conjugation (![heavyVector 0, heavyVector 1] i) =
      ![heavyVector 2, heavyVector 3] i := by
    fin_cases i <;> exact Prod.ext (map_zero _)
      (coordinateConjugation_basis _ swapHeavy_involutive _)

  simp only [hn, (conjugation_fields c _).1]
  rfl

theorem hc_D (c : Fin 3) : hc (D c) = -Db c := by
  rw [D, include_down, hc_down]
  simp only [show ∀ c r, conjugation (d c r, 0) = (db c r, 0) from
    fun c r => (conjugation_fields c r).2.1,
    show ∀ c r, conjugation (s c r, 0) = (sb c r, 0) from
      fun c r => (conjugation_fields c r).2.2]
  rw [Db, include_down]

local instance : StarRing B := starRing conjugation conjugation_involutive
local instance : StarModule ℂ B := starModule conjugation conjugation_involutive

/-- Exact scalar-eliminated literal H.c. action on the concrete Grassmann carrier. -/
def literalEffective (m M a b : ℂ) : B :=
  DevMohapatraHermitian.effectiveAction m M a b ![heavy 0, heavy 1] U D

theorem star_dictionary (x : B) : star x = hc x := rfl

theorem U_apply (c : Fin 3) : U c =
    heavy 0*includeExternal (ExteriorAlgebra.ι ℂ (u c 1)) -
      heavy 1*includeExternal (ExteriorAlgebra.ι ℂ (u c 0)) := by
  simp [U, pair, uw, heavy, includeExternal, ExteriorAlgebra.map_apply_ι]

theorem Ub_apply (c : Fin 3) : Ub c =
    heavy 2*includeExternal (ExteriorAlgebra.ι ℂ (ub c 1)) -
      heavy 3*includeExternal (ExteriorAlgebra.ι ℂ (ub c 0)) := by
  simp [Ub, pair, ubw, heavy, includeExternal, ExteriorAlgebra.map_apply_ι]

theorem sum_U_D : ∑ c, U c*D c =
    heavy 0*includeExternal (current u d s 1)-heavy 1*includeExternal (current u d s 0) := by
  simp only [D, include_down]
  change (∑ c, nuVertex uw ![heavy 0, heavy 1] c * downCurrent dw sw c) = _
  rw [nuVertex_sum, include_current, include_current]
  rfl

theorem sum_Ub_Db : ∑ c, Ub c*Db c =
    heavy 2*includeExternal (current ub db sb 1)-heavy 3*includeExternal (current ub db sb 0) := by
  simp only [Db, include_down]
  change (∑ c, nuVertex ubw ![heavy 2, heavy 3] c * downCurrent dbw sbw c) = _
  rw [nuVertex_sum, include_current, include_current]
  rfl

theorem Db_commutes (c : Fin 3) (x : B) : Db c*x = x*Db c := by
  apply Math.ExteriorOdd.even_central
  simp [Db, includeExternal, ExteriorAlgebra.map_apply_ι, downCurrent, pair, map_sum, map_mul, CliffordAlgebra.involute_ι]

theorem mixed_color (c : Fin 3) : U c*Ub c =
    -heavy 0*heavy 2*includeExternal (ExteriorAlgebra.ι ℂ (u c 1)*ExteriorAlgebra.ι ℂ (ub c 1)) +
      heavy 0*heavy 3*includeExternal (ExteriorAlgebra.ι ℂ (u c 1)*ExteriorAlgebra.ι ℂ (ub c 0)) +
      heavy 1*heavy 2*includeExternal (ExteriorAlgebra.ι ℂ (u c 0)*ExteriorAlgebra.ι ℂ (ub c 1)) -
      heavy 1*heavy 3*includeExternal (ExteriorAlgebra.ι ℂ (u c 0)*ExteriorAlgebra.ι ℂ (ub c 0)) := by
  have hs (r : Fin 2) (j : Fin 4) (z : B) :
      includeExternal (ExteriorAlgebra.ι ℂ (u c r))*(heavy j*z) =
        -(heavy j*(includeExternal (ExteriorAlgebra.ι ℂ (u c r))*z)) := by
    have h : includeExternal (ExteriorAlgebra.ι ℂ (u c r))*heavy j =
        -(heavy j*includeExternal (ExteriorAlgebra.ι ℂ (u c r))) := by
      apply Math.ExteriorOdd.anticommute
      · simp [Math.ExteriorOdd.Odd, includeExternal, ExteriorAlgebra.map_apply_ι,
          CliffordAlgebra.involute_ι]
      · exact heavy_odd j
    rw [← mul_assoc, h, neg_mul, mul_assoc]
  simp only [U_apply, Ub_apply, mul_sub, sub_mul, mul_assoc, hs, mul_neg, neg_mul, map_mul]
  noncomm_ring

theorem sum_U_Ub : ∑ c, U c*Ub c =
    -heavy 0*heavy 2*includeExternal (cross 1 1)+heavy 0*heavy 3*includeExternal (cross 1 0)+
      heavy 1*heavy 2*includeExternal (cross 0 1)-heavy 1*heavy 3*includeExternal (cross 0 0) := by
  simp [mixed_color, cross, map_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, ← mul_assoc]

theorem constant_dictionary (m b : ℂ) : includeExternal (constant m b) =
    (star b*b/m) • ∑ c, D c*Db c := by
  simp only [constant, map_smul, map_sum, map_mul]
  change (star b*b/m) • (∑ c, Db c*D c) = _
  simp only [Db_commutes]

/-- The exact quadratic action differentiated in HeavyAction is the literal
H.c. scalar-eliminated action, on the constructed complex star carrier. -/
theorem action_dictionary (m M a b : ℂ) :
    literalEffective m M a b = universalAction m M a b := by
  have hn : heavy 3*heavy 2 = -(heavy 2*heavy 3) :=
    Math.ExteriorOdd.anticommute _ _ (heavy_odd 3) (heavy_odd 2)
  have hmass : DevMohapatraHermitian.massAction M ![heavy 0, heavy 1] =
      -M • (heavy 0*heavy 1) + star M • (heavy 2*heavy 3) := by
    simp [DevMohapatraHermitian.massAction, star_dictionary, hc_mul,
      hc_heavy, swapHeavy, hn]
  simp only [literalEffective, DevMohapatraHermitian.effectiveAction, hmass,
    DevMohapatraHermitian.effective_expansion, star_dictionary, hc_U, hc_D,
    mul_neg, neg_mul, smul_neg, neg_neg]
  simp only [Finset.sum_sub_distrib, ← Finset.smul_sum,
    Db_commutes, sum_U_D, sum_Ub_Db]
  simp only [Finset.sum_neg_distrib, ← Finset.smul_sum, sum_U_Ub]
  simp only [universalAction, constant_dictionary]
  module

/-- The original Hermitian UV action after exact scalar elimination. -/
theorem literal_scalar_elimination (m M a b : ℂ) (hm : m ≠ 0) (hmreal : star m = m) :
    DevMohapatraHermitian.action m M a b ![heavy 0, heavy 1] U D
      (fun i => Math.AlgebraValuedQuadraticElimination.solution m 1
        (DevMohapatraHermitian.leftSource a b (U i) (D i))) = universalAction m M a b := by
  rw [DevMohapatraHermitian.action_scalar_on_shell m M a b hm hmreal]
  exact action_dictionary m M a b

theorem universal_hermitian (m M a b : ℂ) (hmreal : star m = m) :
    hc (universalAction m M a b) = universalAction m M a b := by
  rw [← action_dictionary]
  change star (literalEffective m M a b) = literalEffective m M a b
  exact DevMohapatraHermitian.action_effective_hermitian m M a b hmreal _ _ _

theorem full_stationary (m M a b : ℂ) (hM : M ≠ 0) (i : Fin 4) :
    evaluate (solution m M a b) (solution_odd m M a b)
      (derivative i (literalEffective m M a b)) = 0 := by
  rw [action_dictionary]
  exact DevMohapatraHeavyAction.stationary m M a b hM i

theorem full_eliminated_action (m M a b : ℂ) (hm : m ≠ 0)
    (hM : M ≠ 0) (hmreal : star m = m) :
    evaluate (solution m M a b) (solution_odd m M a b)
      (DevMohapatraHermitian.action m M a b ![heavy 0, heavy 1] U D
        (fun i => Math.AlgebraValuedQuadraticElimination.solution m 1
          (DevMohapatraHermitian.leftSource a b (U i) (D i)))) =
      (1/2 : ℂ) • linear m a b (solution m M a b) + constant m b := by
  rw [literal_scalar_elimination m M a b hm hmreal]
  exact DevMohapatraHeavyAction.eliminated_action m M a b hM

theorem holomorphic_full_action (m M a b : ℂ) (hm : m ≠ 0)
    (hM : M ≠ 0) (hmreal : star m = m) :
    DevMohapatraHeavyProjection.project
      (evaluate (solution m M a b) (solution_odd m M a b)
        (DevMohapatraHermitian.action m M a b ![heavy 0, heavy 1] U D
          (fun i => Math.AlgebraValuedQuadraticElimination.solution m 1
            (DevMohapatraHermitian.leftSource a b (U i) (D i))))) =
      generated m M a b DevMohapatraHeavyProjection.ul
        DevMohapatraHeavyProjection.dl DevMohapatraHeavyProjection.sl := by
  rw [literal_scalar_elimination m M a b hm hmreal, evaluated_action]
  exact DevMohapatraHeavyProjection.project_eliminated_action m M a b hM

end
end GUT.DevMohapatraHeavyHermitian
