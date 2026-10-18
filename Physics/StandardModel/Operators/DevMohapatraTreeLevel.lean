import Physics.StandardModel.Operators.DevMohapatraConnection
import Math.LinearAlgebra.AlgebraValuedQuadraticElimination
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! One-N derivative-free selected-channel elimination with explicit Grassmann
vertices. This action convention is supplied, not inferred from suppressed
spinor and flavor sums in the literature. -/
namespace GUT.DevMohapatraTreeLevel
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
noncomputable section
open Math SMEpsilonTensor
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
abbrev A (V : Type*) [AddCommGroup V] [Module ℂ V] := ExteriorAlgebra ℂ V

def pair (x y : Fin 2 → V) : A V :=
  ExteriorAlgebra.ι ℂ (x 0) * ExteriorAlgebra.ι ℂ (y 1) -
    ExteriorAlgebra.ι ℂ (x 1) * ExteriorAlgebra.ι ℂ (y 0)

theorem pair_symmetric (x y : Fin 2 → V) : pair x y = pair y x := by
  have h₁ := eq_neg_of_add_eq_zero_left
    (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (x 0) (y 1))
  have h₂ := eq_neg_of_add_eq_zero_left
    (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (x 1) (y 0))
  simp only [pair, h₁, h₂]
  abel

theorem majorana_half (m : ℂ) (n : Fin 2 → V) :
    -(m / 2) • pair n n = -m •
      (ExteriorAlgebra.ι ℂ (n 0) * ExteriorAlgebra.ι ℂ (n 1)) := by
  have h := eq_neg_of_add_eq_zero_left
    (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (n 1) (n 0))
  simp only [pair, h, sub_neg_eq_add, smul_add]
  module

/-- The literal uu/ds/ds order differs by one fermion swap from the older
U,D,U,S,D,S coefficient-space slot convention. -/
theorem source_generator_order (u v d s e t : V) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ d *
      ExteriorAlgebra.ι ℂ s * ExteriorAlgebra.ι ℂ e * ExteriorAlgebra.ι ℂ t =
    -(ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ d * ExteriorAlgebra.ι ℂ v *
      ExteriorAlgebra.ι ℂ s * ExteriorAlgebra.ι ℂ e * ExteriorAlgebra.ι ℂ t) := by
  have h := eq_neg_of_add_eq_zero_left
    (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) v d)
  have he : ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ d =
      -(ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ d * ExteriorAlgebra.ι ℂ v) := by
    rw [mul_assoc, h, mul_neg, ← mul_assoc]
  rw [he]
  simp only [neg_mul]

def cubic (u d s : V) : A V := ExteriorAlgebra.ιMulti ℂ 3 ![u,d,s]

theorem cubic_apply (u d s : V) : cubic u d s =
    ExteriorAlgebra.ι ℂ u *
      (ExteriorAlgebra.ι ℂ d * ExteriorAlgebra.ι ℂ s) := by
  simp [cubic, ExteriorAlgebra.ιMulti_apply]

theorem cubic_swap (u d s v e t : V) :
    cubic u d s * cubic v e t = -(cubic v e t * cubic u d s) := by
  simpa only [show ((-1 : ℤˣ) ^ (3 * 3)) = -1 from by decide,
    Units.neg_smul, one_smul, cubic] using
    (ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm (R := ℂ) ![u,d,s] ![v,e,t])

theorem generator_cubic_swap (v u d s : V) :
    ExteriorAlgebra.ι ℂ v * cubic u d s = -(cubic u d s * ExteriorAlgebra.ι ℂ v) := by
  simpa only [show ((-1 : ℤˣ) ^ 3) = -1 from by decide,
    Units.neg_smul, one_smul, cubic] using
    (ExteriorAlgebra.ι_mul_ιMulti_anticomm (R := ℂ) v ![u,d,s])

theorem even_product_commutes (x y z : V) :
    (ExteriorAlgebra.ι ℂ x * ExteriorAlgebra.ι ℂ y) * ExteriorAlgebra.ι ℂ z =
      ExteriorAlgebra.ι ℂ z * (ExteriorAlgebra.ι ℂ x * ExteriorAlgebra.ι ℂ y) := by
  simpa [ExteriorAlgebra.ιMulti_apply] using
    (ExteriorAlgebra.ι_mul_ιMulti_anticomm (R := ℂ) z ![x,y]).symm

theorem pair_commutes (x y : Fin 2 → V) (z : V) :
    pair x y * ExteriorAlgebra.ι ℂ z = ExteriorAlgebra.ι ℂ z * pair x y := by
  simp only [pair, sub_mul, mul_sub, even_product_commutes]

abbrev Index := Fin 3 × Fin 3 × Fin 3 × Fin 2
def colorWeight (i : Index) : ℂ :=
  eps3 (colorBasis i.1) (colorBasis i.2.1) (colorBasis i.2.2.1) *
    (if i.2.2.2 = 0 then 1 else -1)

def term (u d s : Fin 3 → Fin 2 → V) (r : Fin 2) (i : Index) : A V :=
  cubic (u i.1 r) (d i.2.1 i.2.2.2) (s i.2.2.1 (1 - i.2.2.2))

/-- Color epsilon times u_r (d_0 s_1 - d_1 s_0), summed over colors. -/
def current (u d s : Fin 3 → Fin 2 → V) (r : Fin 2) : A V :=
  ∑ i : Index, colorWeight i • term u d s r i

theorem current_swap (u d s : Fin 3 → Fin 2 → V) (r t : Fin 2) :
    current u d s r * current u d s t = -(current u d s t * current u d s r) := by
  classical
  simp only [current, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Finset.smul_sum, smul_smul]
  simp only [← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [term, term, cubic_swap, smul_neg]
  congr 1
  rw [mul_comm]

theorem generator_current_swap (u d s : Fin 3 → Fin 2 → V) (r : Fin 2) (n : V) :
    ExteriorAlgebra.ι ℂ n * current u d s r =
      -(current u d s r * ExteriorAlgebra.ι ℂ n) := by
  classical
  simp only [current, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [term, generator_cubic_swap, smul_neg]

def downCurrent (d s : Fin 3 → Fin 2 → V) (a : Fin 3) : A V :=
  ∑ b, ∑ c, eps3 (colorBasis a) (colorBasis b) (colorBasis c) • pair (d b) (s c)

theorem downCurrent_swap (d s : Fin 3 → Fin 2 → V) (a : Fin 3) :
    downCurrent s d a = -downCurrent d s a := by
  simp only [downCurrent, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  have h : eps3 (colorBasis a) (colorBasis c) (colorBasis b) =
      -eps3 (colorBasis a) (colorBasis b) (colorBasis c) := by
    simp only [eps3]
    ring
  rw [h, pair_symmetric (s c) (d b), neg_smul]

/-- Summing both ordered flavor entries (ds,sd) without a half doubles the
selected vertex. An independent-pair convention instead uses a single entry. -/
theorem ordered_flavor_sum (z : ℂ) (d s : Fin 3 → Fin 2 → V) (a : Fin 3) :
    z • downCurrent d s a + (-z) • downCurrent s d a =
      (2 * z) • downCurrent d s a := by
  rw [downCurrent_swap]
  module

theorem current_color (u d s : Fin 3 → Fin 2 → V) (r : Fin 2) :
    current u d s r = ∑ a, ExteriorAlgebra.ι ℂ (u a r) * downCurrent d s a := by
  classical
  simp only [current, Fintype.sum_prod_type, colorWeight, term]
  simp only [Fin.sum_univ_two, Fin.reduceSub, Fin.reduceEq, ite_true,
    ite_false, mul_one, mul_neg_one, neg_smul, cubic_apply]
  simp only [downCurrent, pair, Finset.mul_sum, mul_smul_comm, mul_sub, smul_sub]
  simp only [sub_eq_add_neg]

theorem scalar_vertex (u d s : Fin 3 → Fin 2 → V) (n : Fin 2 → V) :
    (∑ a, pair n (u a) * downCurrent d s a) =
      ExteriorAlgebra.ι ℂ (n 0) * current u d s 1 -
        ExteriorAlgebra.ι ℂ (n 1) * current u d s 0 := by
  rw [current_color, current_color]
  simp only [pair, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

theorem downCurrent_commutes (d s : Fin 3 → Fin 2 → V) (a : Fin 3) (z : V) :
    downCurrent d s a * ExteriorAlgebra.ι ℂ z =
      ExteriorAlgebra.ι ℂ z * downCurrent d s a := by
  simp only [downCurrent, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, pair_commutes]

theorem current_product (u d s : Fin 3 → Fin 2 → V) (r t : Fin 2) :
    current u d s r * current u d s t =
      ∑ a, ∑ b, (ExteriorAlgebra.ι ℂ (u a r) * ExteriorAlgebra.ι ℂ (u b t)) *
        (downCurrent d s a * downCurrent d s b) := by
  rw [current_color, current_color]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [mul_assoc]
  rw [← mul_assoc (downCurrent d s a), downCurrent_commutes]
  simp only [mul_assoc]

/-- Literal uu/ds/ds Grassmann order; color epsilons are in the two down currents.
This is an explicit contraction, with no matching scalar hidden in it. -/
def printedOperator (u d s : Fin 3 → Fin 2 → V) : A V :=
  ∑ a, ∑ b, pair (u a) (u b) * (downCurrent d s a * downCurrent d s b)

theorem printedOperator_eq (u d s : Fin 3 → Fin 2 → V) :
    printedOperator u d s = (2 : ℂ) • (current u d s 0 * current u d s 1) := by
  have h : printedOperator u d s =
      current u d s 0 * current u d s 1 - current u d s 1 * current u d s 0 := by
    rw [current_product, current_product]
    simp only [printedOperator, pair, sub_mul, Finset.sum_sub_distrib]
  rw [h, current_swap u d s 1 0]
  module

def treePrefactor (mChiSq mN lam lamDS : ℂ) : ℂ :=
  (lam * lamDS) ^ 2 / (2 * mChiSq ^ 2 * mN)

theorem treePrefactor_down_rescaling (mChiSq mN lam lamDS c : ℂ) :
    treePrefactor mChiSq mN lam (c * lamDS) =
      c ^ 2 * treePrefactor mChiSq mN lam lamDS := by
  unfold treePrefactor
  ring


def effectiveCoupling (mChiSq lam lamDS : ℂ) : ℂ := lam * lamDS / mChiSq

/-- The scalar paired action has independently supplied chi and conjugate-chi
coordinates; substitution yields the selected N-u/d-s vertex. -/
theorem scalar_elimination (mChiSq lam lamDS : ℂ) (hm : mChiSq ≠ 0)
    (Nu ds chi chiBar : A V) :
    AlgebraValuedQuadraticElimination.pairedAction mChiSq lam lamDS Nu ds
      (chi + AlgebraValuedQuadraticElimination.solution mChiSq lam Nu)
      (chiBar + AlgebraValuedQuadraticElimination.solution mChiSq lamDS ds) =
    mChiSq • (chi * chiBar) - effectiveCoupling mChiSq lam lamDS • (Nu * ds) := by
  simpa [effectiveCoupling] using
    AlgebraValuedQuadraticElimination.paired_shifted mChiSq lam lamDS hm Nu ds chi chiBar

/-- Sum the three scalar colors before the Majorana elimination. -/
theorem scalar_on_shell (mChiSq lam lamDS : ℂ) (hm : mChiSq ≠ 0)
    (u d s : Fin 3 → Fin 2 → V) (n : Fin 2 → V) :
    (∑ a, AlgebraValuedQuadraticElimination.pairedAction mChiSq lam lamDS
      (pair n (u a)) (downCurrent d s a)
      (AlgebraValuedQuadraticElimination.solution mChiSq lam (pair n (u a)))
      (AlgebraValuedQuadraticElimination.solution mChiSq lamDS (downCurrent d s a))) =
    -effectiveCoupling mChiSq lam lamDS •
      (ExteriorAlgebra.ι ℂ (n 0) * current u d s 1 -
        ExteriorAlgebra.ι ℂ (n 1) * current u d s 0) := by
  simp_rw [AlgebraValuedQuadraticElimination.paired_on_shell _ _ _ hm]
  rw [← Finset.smul_sum, scalar_vertex]
  rfl

theorem majorana_elimination (mN g : ℂ) (hm : mN ≠ 0)
    (u d s : Fin 3 → Fin 2 → V) (n : Fin 2 → V) :
    AlgebraValuedQuadraticElimination.majoranaAction mN g
      (current u d s 0) (current u d s 1)
      (ExteriorAlgebra.ι ℂ (n 0) +
        AlgebraValuedQuadraticElimination.solution mN g (current u d s 0))
      (ExteriorAlgebra.ι ℂ (n 1) +
        AlgebraValuedQuadraticElimination.solution mN g (current u d s 1)) =
    -mN • (ExteriorAlgebra.ι ℂ (n 0) * ExteriorAlgebra.ι ℂ (n 1)) +
      (g ^ 2 / mN) • (current u d s 0 * current u d s 1) :=
  AlgebraValuedQuadraticElimination.majorana_shifted mN g hm _ _ _ _
    (current_swap u d s 1 0) (generator_current_swap u d s 0 (n 1))

def generated (mChiSq mN lam lamDS : ℂ) (u d s : Fin 3 → Fin 2 → V) : A V :=
  ((effectiveCoupling mChiSq lam lamDS) ^ 2 / mN) •
    (current u d s 0 * current u d s 1)

def nuVertex (u : Fin 3 → Fin 2 → V) (n : Fin 2 → A V) (a : Fin 3) : A V :=
  n 0 * ExteriorAlgebra.ι ℂ (u a 1) - n 1 * ExteriorAlgebra.ι ℂ (u a 0)

theorem nuVertex_sum (u d s : Fin 3 → Fin 2 → V) (n : Fin 2 → A V) :
    (∑ a, nuVertex u n a * downCurrent d s a) =
      n 0 * current u d s 1 - n 1 * current u d s 0 := by
  rw [current_color, current_color]
  simp only [nuVertex, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

/-- Supplied derivative-free chiral UV action. Conjugate vertices and kinetic
terms are excluded from this holomorphic six-quark matching component. -/
def uvAction (mChiSq mN lam lamDS : ℂ) (u d s : Fin 3 → Fin 2 → V)
    (n : Fin 2 → A V) (chi chiBar : Fin 3 → A V) : A V :=
  -mN • (n 0 * n 1) + ∑ a,
    AlgebraValuedQuadraticElimination.pairedAction mChiSq lam lamDS
      (nuVertex u n a) (downCurrent d s a) (chi a) (chiBar a)

def chiSolution (mChiSq lam : ℂ) (u : Fin 3 → Fin 2 → V) (n : Fin 2 → A V)
    (a : Fin 3) : A V :=
  AlgebraValuedQuadraticElimination.solution mChiSq lam (nuVertex u n a)

def chiBarSolution (mChiSq lamDS : ℂ) (d s : Fin 3 → Fin 2 → V) (a : Fin 3) : A V :=
  AlgebraValuedQuadraticElimination.solution mChiSq lamDS (downCurrent d s a)

def nSolution (mChiSq mN lam lamDS : ℂ) (u d s : Fin 3 → Fin 2 → V)
    (r : Fin 2) : A V :=
  AlgebraValuedQuadraticElimination.solution mN (effectiveCoupling mChiSq lam lamDS)
    (current u d s r)

theorem uv_after_scalar (mChiSq mN lam lamDS : ℂ) (hc : mChiSq ≠ 0)
    (u d s : Fin 3 → Fin 2 → V) (n : Fin 2 → A V) :
    uvAction mChiSq mN lam lamDS u d s n
      (chiSolution mChiSq lam u n) (chiBarSolution mChiSq lamDS d s) =
    AlgebraValuedQuadraticElimination.majoranaAction mN
      (effectiveCoupling mChiSq lam lamDS) (current u d s 0) (current u d s 1)
      (n 0) (n 1) := by
  simp only [uvAction, chiSolution, chiBarSolution,
    AlgebraValuedQuadraticElimination.paired_on_shell _ _ _ hc]
  rw [← Finset.smul_sum, nuVertex_sum]
  simp only [AlgebraValuedQuadraticElimination.majoranaAction, effectiveCoupling,
    neg_smul, sub_eq_add_neg]

/-- Exact sequential on-shell value of the explicit supplied UV action. -/
theorem uv_sequential_on_shell (mChiSq mN lam lamDS : ℂ)
    (hc : mChiSq ≠ 0) (hn : mN ≠ 0) (u d s : Fin 3 → Fin 2 → V) :
    uvAction mChiSq mN lam lamDS u d s (nSolution mChiSq mN lam lamDS u d s)
      (chiSolution mChiSq lam u (nSolution mChiSq mN lam lamDS u d s))
      (chiBarSolution mChiSq lamDS d s) = generated mChiSq mN lam lamDS u d s := by
  rw [uv_after_scalar _ _ _ _ hc]
  exact AlgebraValuedQuadraticElimination.majorana_on_shell _ _ hn _ _
    (current_swap u d s 1 0)

theorem generated_on_shell (mChiSq mN lam lamDS : ℂ) (hm : mN ≠ 0)
    (u d s : Fin 3 → Fin 2 → V) :
    AlgebraValuedQuadraticElimination.majoranaAction mN
      (effectiveCoupling mChiSq lam lamDS) (current u d s 0) (current u d s 1)
      (AlgebraValuedQuadraticElimination.solution mN
        (effectiveCoupling mChiSq lam lamDS) (current u d s 0))
      (AlgebraValuedQuadraticElimination.solution mN
        (effectiveCoupling mChiSq lam lamDS) (current u d s 1)) =
      generated mChiSq mN lam lamDS u d s :=
  AlgebraValuedQuadraticElimination.majorana_on_shell _ _ hm _ _ (current_swap u d s 1 0)

theorem generated_printed (mChiSq mN lam lamDS : ℂ)
    (u d s : Fin 3 → Fin 2 → V) :
    generated mChiSq mN lam lamDS u d s =
      treePrefactor mChiSq mN lam lamDS • printedOperator u d s := by
  rw [printedOperator_eq]
  simp only [generated, effectiveCoupling, treePrefactor, smul_smul]
  congr 1
  ring

abbrev ProbeSpace := Fin 6 → ℂ

def probeU (a : Fin 3) (r : Fin 2) : ProbeSpace :=
  if a = 0 ∧ r = 0 then Pi.single 0 1 else
  if a = 2 ∧ r = 1 then Pi.single 2 1 else 0

def probeD (a : Fin 3) (r : Fin 2) : ProbeSpace :=
  if a = 2 ∧ r = 0 then Pi.single 1 1 else
  if a = 0 ∧ r = 1 then Pi.single 4 1 else 0

def probeS (a : Fin 3) (r : Fin 2) : ProbeSpace :=
  if a = 1 ∧ r = 0 then Pi.single 3 1 else
  if a = 1 ∧ r = 1 then Pi.single 5 1 else 0

theorem probe_current_zero : current probeU probeD probeS 0 =
    -cubic (Pi.single 0 1 : ProbeSpace) (Pi.single 1 1) (Pi.single 5 1) := by
  rw [current_color]
  norm_num [downCurrent, pair, probeU, probeD, probeS, eps3, colorBasis,
    Fin.sum_univ_succ, Pi.single_apply, cubic_apply]

theorem probe_current_one : current probeU probeD probeS 1 =
    -cubic (Pi.single 2 1 : ProbeSpace) (Pi.single 4 1) (Pi.single 3 1) := by
  rw [current_color]
  norm_num [downCurrent, pair, probeU, probeD, probeS, eps3, colorBasis,
    Fin.sum_univ_succ, Pi.single_apply, cubic_apply]

def probeCoefficient : A ProbeSpace →ₗ[ℂ] ℂ :=
  ExteriorAlgebra.liftAlternating (Function.update (fun n =>
    (0 : ProbeSpace [⋀^Fin n]→ₗ[ℂ] ℂ)) 6 (Pi.basisFun ℂ (Fin 6)).det)

theorem probe_product_evaluation :
    probeCoefficient (current probeU probeD probeS 0 * current probeU probeD probeS 1) = 1 := by
  rw [probe_current_zero, probe_current_one, neg_mul_neg]
  unfold cubic
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
  rw [probeCoefficient, ExteriorAlgebra.liftAlternating_apply_ιMulti]
  simp only [Function.update_self]
  have hv : Fin.append (![Pi.single 0 1,Pi.single 1 1,Pi.single 5 1] : Fin 3 → ProbeSpace)
      ![Pi.single 2 1,Pi.single 4 1,Pi.single 3 1] =
      (Pi.basisFun ℂ (Fin 6)) ∘ (Equiv.swap (2 : Fin 6) 5 * Equiv.swap (3 : Fin 6) 5) := by
    ext i j
    fin_cases i <;> simp [Equiv.swap_apply_def, Pi.basisFun_apply,
      Fin.append, Fin.addCases]
  rw [hv, AlternatingMap.map_perm]
  have hs : Equiv.Perm.sign (Equiv.swap (2 : Fin 6) 5 * Equiv.swap (3 : Fin 6) 5) = 1 := by simp
  rw [hs, one_smul]
  exact Module.Basis.det_self _

theorem probe_printed_evaluation :
    probeCoefficient (printedOperator probeU probeD probeS) = 2 := by
  rw [printedOperator_eq, map_smul, probe_product_evaluation]
  norm_num

theorem probe_generated_evaluation (mChiSq mN lam lamDS : ℂ) :
    probeCoefficient (generated mChiSq mN lam lamDS probeU probeD probeS) =
      (lam * lamDS) ^ 2 / (mChiSq ^ 2 * mN) := by
  simp only [generated, map_smul, probe_product_evaluation, smul_eq_mul, mul_one,
    effectiveCoupling]
  ring

theorem probe_generated_nonzero (mChiSq mN lam lamDS : ℂ)
    (hc : mChiSq ≠ 0) (hn : mN ≠ 0) (hl : lam ≠ 0) (hd : lamDS ≠ 0) :
    generated mChiSq mN lam lamDS probeU probeD probeS ≠ 0 := by
  intro h
  have he := probe_generated_evaluation mChiSq mN lam lamDS
  rw [h, map_zero] at he
  exact (div_ne_zero (pow_ne_zero 2 (mul_ne_zero hl hd))
    (mul_ne_zero (pow_ne_zero 2 hc) hn)) he.symm

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem map_current (f : V →ₗ[ℂ] W) (u d s : Fin 3 → Fin 2 → V) (r : Fin 2) :
    ExteriorAlgebra.map f (current u d s r) =
      current (fun a t => f (u a t)) (fun a t => f (d a t)) (fun a t => f (s a t)) r := by
  simp only [current, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp only [term, cubic, ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  ext j
  fin_cases j <;> rfl

abbrev Coordinates := Fin 3 × Fin 3 × Fin 2 → ℂ

/-- Species 0,1,2 are u,d,s. These are independent Grassmann generators. -/
def field (species : Fin 3) (a : Fin 3) (r : Fin 2) : Coordinates :=
  Pi.single (species,a,r) 1

def restriction : Coordinates →ₗ[ℂ] ProbeSpace where
  toFun x := ![x (0,0,0), x (1,2,0), x (0,2,1), x (2,1,0), x (1,0,1), x (2,1,1)]
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' z x := by ext i; fin_cases i <;> rfl

theorem restriction_field_u (a : Fin 3) (r : Fin 2) :
    restriction (field 0 a r) = probeU a r := by
  ext i
  fin_cases a <;> fin_cases r <;> fin_cases i <;>
    norm_num [restriction, field, probeU, Pi.single_apply]

theorem restriction_field_d (a : Fin 3) (r : Fin 2) :
    restriction (field 1 a r) = probeD a r := by
  ext i
  fin_cases a <;> fin_cases r <;> fin_cases i <;>
    norm_num [restriction, field, probeD, Pi.single_apply]

theorem restriction_field_s (a : Fin 3) (r : Fin 2) :
    restriction (field 2 a r) = probeS a r := by
  ext i
  fin_cases a <;> fin_cases r <;> fin_cases i <;>
    norm_num [restriction, field, probeS, Pi.single_apply]

theorem restriction_generated (mChiSq mN lam lamDS : ℂ) :
    ExteriorAlgebra.map restriction (generated mChiSq mN lam lamDS (field 0) (field 1) (field 2)) =
      generated mChiSq mN lam lamDS probeU probeD probeS := by
  simp only [generated, map_smul, map_mul, map_current,
    restriction_field_u, restriction_field_d, restriction_field_s]

/-- Nonzero generated six-quark term on all eighteen selected-flavor components,
not merely nonzero ordered tensor data. -/
theorem generated_nonzero (mChiSq mN lam lamDS : ℂ)
    (hc : mChiSq ≠ 0) (hn : mN ≠ 0) (hl : lam ≠ 0) (hd : lamDS ≠ 0) :
    generated mChiSq mN lam lamDS (field 0) (field 1) (field 2) ≠ 0 := by
  intro h
  have hr := restriction_generated mChiSq mN lam lamDS
  rw [h, map_zero] at hr
  exact probe_generated_nonzero mChiSq mN lam lamDS hc hn hl hd hr.symm

/-- Literal Eq.(4) scalar after writing Mchi^4 as mChiSq^2. Identification of
the paper's lambda-prime with the selected vertex lamDS remains external. -/
def paperPrefactor (mChiSq mN lam lamDS : ℂ) : ℂ :=
  (lam * lamDS) ^ 2 / (16 * (Real.pi : ℂ) ^ 2 * mChiSq ^ 2 * mN)

theorem prefactor_comparison (mChiSq mN lam lamDS : ℂ)
    (hc : mChiSq ≠ 0) (hn : mN ≠ 0) :
    treePrefactor mChiSq mN lam lamDS =
      (8 * (Real.pi : ℂ) ^ 2) * paperPrefactor mChiSq mN lam lamDS := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold treePrefactor paperPrefactor
  field_simp [hc, hn, hp]
  ring

/-- Conditional comparison of the supplied action dictionary with the printed
scalar, not an assertion that the paper uses this dictionary. -/
theorem prefactors_ne (mChiSq mN lam lamDS : ℂ)
    (hc : mChiSq ≠ 0) (hn : mN ≠ 0) (hl : lam ≠ 0) (hd : lamDS ≠ 0) :
    treePrefactor mChiSq mN lam lamDS ≠ paperPrefactor mChiSq mN lam lamDS := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpaper : paperPrefactor mChiSq mN lam lamDS ≠ 0 := by
    exact div_ne_zero (pow_ne_zero 2 (mul_ne_zero hl hd))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp))
        (pow_ne_zero 2 hc)) hn)
  have hfactor : (8 * (Real.pi : ℂ) ^ 2) ≠ 1 := by
    have hreal : (8 * Real.pi ^ 2 : ℝ) ≠ 1 := by
      have hpi := Real.two_le_pi
      nlinarith
    exact_mod_cast hreal
  intro he
  rw [prefactor_comparison mChiSq mN lam lamDS hc hn] at he
  exact hfactor ((mul_eq_right₀ hpaper).mp he)

end
end GUT.DevMohapatraTreeLevel
