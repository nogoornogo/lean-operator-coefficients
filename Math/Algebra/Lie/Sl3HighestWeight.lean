import Math.Algebra.Lie.Sl2String
import Math.Algebra.Lie.StandardSl3
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

/-!
# Low-dimensional highest-weight analysis for `sl₃(ℂ)`

This file develops the part of the `SU(3)` highest-weight theorem actually
needed by semisimple embedding classification.  Starting from one highest-weight vector for the two concrete
simple-root triples in `StandardSl3`, it constructs the three lowering
strings and records their simultaneous Cartan weights.

The construction is deliberately algebraic.  The separate analytic bridge
must still differentiate an intended `SU(3)` group representation and
produce such a highest-weight vector.
-/

namespace Math
namespace Sl3HighestWeight

open LieModule
open StandardSl3

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable [LieRingModule Algebra V] [LieModule ℂ Algebra V]

/-- A simultaneous eigenvector for the two standard Cartan generators. -/
structure HasCartanWeight (v : V) (a b : ℂ) : Prop where
  lie_H1 : ⁅H1, v⁆ = a • v
  lie_H2 : ⁅H2, v⁆ = b • v

/-- A dominant integral highest-weight vector for the two standard simple
roots of `sl₃(ℂ)`. -/
structure HighestWeightVector (v : V) (a b : ℕ) : Prop
    extends HasCartanWeight v (a : ℂ) (b : ℂ) where
  ne_zero : v ≠ 0
  lie_E1 : ⁅E1, v⁆ = 0
  lie_E2 : ⁅E2, v⁆ = 0

namespace HighestWeightVector

variable {v : V} {a b : ℕ}

omit [LieModule ℂ (↥StandardSl3.Algebra) V] in
theorem lie_E12 (P : HighestWeightVector v a b) : ⁅E12, v⁆ = 0 := by
  rw [← lie_E1_E2]
  have h := leibniz_lie E1 E2 v
  rw [P.lie_E2, lie_zero, P.lie_E1, lie_zero, add_zero] at h
  exact h.symm

omit [LieModule ℂ (↥StandardSl3.Algebra) V] in
/-- The highest vector is primitive for the first simple-root `sl₂`. -/
theorem firstPrimitive (P : HighestWeightVector v a b) :
    firstIsSl2Triple.HasPrimitiveVectorWith v (a : ℂ) where
  ne_zero := P.ne_zero
  lie_h := P.lie_H1
  lie_e := P.lie_E1

omit [LieModule ℂ (↥StandardSl3.Algebra) V] in
/-- The highest vector is primitive for the second simple-root `sl₂`. -/
theorem secondPrimitive (P : HighestWeightVector v a b) :
    secondIsSl2Triple.HasPrimitiveVectorWith v (b : ℂ) where
  ne_zero := P.ne_zero
  lie_h := P.lie_H2
  lie_e := P.lie_E2

omit [LieModule ℂ (↥StandardSl3.Algebra) V] in
/-- The highest vector is also primitive for the composite-root `sl₂`, of
highest weight `a+b`. -/
theorem compositePrimitive (P : HighestWeightVector v a b) :
    compositeIsSl2Triple.HasPrimitiveVectorWith v ((a + b : ℕ) : ℂ) where
  ne_zero := P.ne_zero
  lie_h := by
    rw [add_lie, P.lie_H1, P.lie_H2, ← add_smul, Nat.cast_add]
  lie_e := P.lie_E12

end HighestWeightVector

/-- Repeated action by a lowering root vector. -/
def lower (F : Algebra) (n : ℕ) (v : V) : V :=
  ((toEnd ℂ Algebra V F) ^ n) v

@[simp]
theorem lower_zero (F : Algebra) (v : V) : lower F 0 v = v := by
  simp [lower]

theorem lower_succ (F : Algebra) (n : ℕ) (v : V) :
    lower F (n + 1) v = ⁅F, lower F n v⁆ := by
  simp [lower, pow_succ', Module.End.mul_apply]

/-- Iterating a root vector shifts an eigenvalue by the corresponding root
value at every step. -/
theorem lie_lower_of_eigen
    {H F : Algebra} {v : V} {c lambda : ℂ}
    (hHF : ⁅H, F⁆ = c • F)
    (hv : ⁅H, v⁆ = lambda • v) :
    ∀ n : ℕ, ⁅H, lower F n v⁆ =
      (lambda + (n : ℂ) * c) • lower F n v := by
  intro n
  induction n with
  | zero => simpa using hv
  | succ n ih =>
      rw [lower_succ, leibniz_lie, hHF, smul_lie, ih, lie_smul, ← add_smul]
      congr 1
      push_cast
      ring

theorem lower_F1_hasCartanWeight
    {v : V} {a b : ℂ} (P : HasCartanWeight v a b) (n : ℕ) :
    HasCartanWeight (lower F1 n v) (a - 2 * n) (b + n) where
  lie_H1 := by
    have hHF : ⁅H1, F1⁆ = (-2 : ℂ) • F1 := by
      simpa using firstIsSl2Triple.lie_lie_smul_f (R := ℂ)
    simpa [sub_eq_add_neg, mul_comm] using
      lie_lower_of_eigen hHF P.lie_H1 n
  lie_H2 := by
    have hHF : ⁅H2, F1⁆ = (1 : ℂ) • F1 := by
      simpa using lie_H2_F1
    simpa using lie_lower_of_eigen hHF P.lie_H2 n

theorem lower_F2_hasCartanWeight
    {v : V} {a b : ℂ} (P : HasCartanWeight v a b) (n : ℕ) :
    HasCartanWeight (lower F2 n v) (a + n) (b - 2 * n) where
  lie_H1 := by
    have hHF : ⁅H1, F2⁆ = (1 : ℂ) • F2 := by
      simpa using lie_H1_F2
    simpa using lie_lower_of_eigen hHF P.lie_H1 n
  lie_H2 := by
    have hHF : ⁅H2, F2⁆ = (-2 : ℂ) • F2 := by
      simpa using secondIsSl2Triple.lie_lie_smul_f (R := ℂ)
    simpa [sub_eq_add_neg, mul_comm] using
      lie_lower_of_eigen hHF P.lie_H2 n

theorem lower_F12_hasCartanWeight
    {v : V} {a b : ℂ} (P : HasCartanWeight v a b) (n : ℕ) :
    HasCartanWeight (lower F12 n v) (a - n) (b - n) where
  lie_H1 := by
    have hHF : ⁅H1, F12⁆ = (-1 : ℂ) • F12 := by
      simpa using lie_H1_F12
    simpa [sub_eq_add_neg] using lie_lower_of_eigen hHF P.lie_H1 n
  lie_H2 := by
    have hHF : ⁅H2, F12⁆ = (-1 : ℂ) • F12 := by
      simpa using lie_H2_F12
    simpa [sub_eq_add_neg] using lie_lower_of_eigen hHF P.lie_H2 n

/-!
## The three lowering rays
-/

/-- The highest vector, followed by the nontrivial points of the first,
second, and composite lowering strings. -/
abbrev RayIndex (a b : ℕ) :=
  Unit ⊕ Fin a ⊕ Fin b ⊕ Fin (a + b)

/-- The integral pair of Cartan eigenvalues attached to a lowering-ray
index. -/
def rayWeight (a b : ℕ) : RayIndex a b → ℤ × ℤ
  | .inl _ => (a, b)
  | .inr (.inl i) => (a - 2 * (i + 1), b + (i + 1))
  | .inr (.inr (.inl j)) => (a + (j + 1), b - 2 * (j + 1))
  | .inr (.inr (.inr k)) => (a - (k + 1), b - (k + 1))

theorem rayWeight_injective (a b : ℕ) :
    Function.Injective (rayWeight a b) := by
  intro x y h
  rcases x with (_ | i | j | k) <;>
    rcases y with (_ | i' | j' | k') <;>
    simp [rayWeight] at h ⊢ <;>
    try { apply Fin.ext } <;>
    omega

/-- Encode a pair of integral Cartan weights as one complex eigenvalue.  The
real and imaginary parts retain both coordinates. -/
def encodeWeight (p : ℤ × ℤ) : ℂ :=
  (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

theorem encodeWeight_injective : Function.Injective encodeWeight := by
  intro p q h
  apply Prod.ext
  · have hr := congrArg Complex.re h
    exact_mod_cast (by simpa [encodeWeight] using hr)
  · have hi := congrArg Complex.im h
    exact_mod_cast (by simpa [encodeWeight] using hi)

/-- The actual vectors indexed by the three nontrivial lowering rays. -/
def rayVector (v : V) (a b : ℕ) : RayIndex a b → V
  | .inl _ => v
  | .inr (.inl i) => lower F1 (i + 1) v
  | .inr (.inr (.inl j)) => lower F2 (j + 1) v
  | .inr (.inr (.inr k)) => lower F12 (k + 1) v

theorem rayVector_hasCartanWeight
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b)
    (i : RayIndex a b) :
    HasCartanWeight (rayVector v a b i)
      ((rayWeight a b i).1 : ℂ) ((rayWeight a b i).2 : ℂ) := by
  rcases i with (_ | i | j | k)
  · simpa [rayVector, rayWeight] using P.toHasCartanWeight
  · simpa [rayVector, rayWeight, sub_eq_add_neg] using
      lower_F1_hasCartanWeight P.toHasCartanWeight (i + 1)
  · simpa [rayVector, rayWeight, sub_eq_add_neg] using
      lower_F2_hasCartanWeight P.toHasCartanWeight (j + 1)
  · simpa [rayVector, rayWeight, sub_eq_add_neg] using
      lower_F12_hasCartanWeight P.toHasCartanWeight (k + 1)

variable [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem rayVector_ne_zero
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b)
    (i : RayIndex a b) :
    rayVector v a b i ≠ 0 := by
  rcases i with (_ | i | j | k)
  · simpa [rayVector] using P.ne_zero
  · simpa [rayVector, lower] using
      P.firstPrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : i + 1 ≤ a)
  · simpa [rayVector, lower] using
      P.secondPrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : j + 1 ≤ b)
  · simpa [rayVector, lower] using
      P.compositePrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl
        (by omega : k + 1 ≤ a + b)

theorem lower_F1_highestWeight_add_one_eq_zero
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b) :
    lower F1 (a + 1) v = 0 := by
  simpa [lower] using
    P.firstPrimitive.pow_toEnd_f_eq_zero_of_eq_nat (R := ℂ) rfl

theorem lower_F2_highestWeight_add_one_eq_zero
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b) :
    lower F2 (b + 1) v = 0 := by
  simpa [lower] using
    P.secondPrimitive.pow_toEnd_f_eq_zero_of_eq_nat (R := ℂ) rfl

theorem lower_F12_highestWeight_add_one_eq_zero
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b) :
    lower F12 (a + b + 1) v = 0 := by
  simpa [lower, Nat.add_assoc] using
    P.compositePrimitive.pow_toEnd_f_eq_zero_of_eq_nat (R := ℂ) rfl

/-! A generator-stability criterion for Lie submodules. -/

/-- A linear subspace stable under the six standard generators is stable under
all of `sl₃(ℂ)`. -/
def lieSubmoduleOfSimpleGeneratorStable
    (W : Submodule ℂ V)
    (hStable : ∀ X ∈ simpleGenerators, ∀ {w : V}, w ∈ W → ⁅X, w⁆ ∈ W) :
    LieSubmodule ℂ Algebra V where
  __ := W
  lie_mem {X} {w} hw := by
    have hAll :
        ∀ X ∈ LieSubalgebra.lieSpan ℂ Algebra simpleGenerators,
          ∀ {w : V}, w ∈ W → ⁅X, w⁆ ∈ W := by
      intro X hX
      induction hX using LieSubalgebra.lieSpan_induction with
      | mem X hX => exact hStable X hX
      | zero => intro w hw; simp
      | add X Y hX hY ihX ihY =>
          intro w hw
          rw [add_lie]
          exact W.add_mem (ihX hw) (ihY hw)
      | smul c X hX ihX =>
          intro w hw
          rw [smul_lie]
          exact W.smul_mem c (ihX hw)
      | lie X Y hX hY ihX ihY =>
          intro w hw
          rw [lie_lie]
          exact W.sub_mem (ihX (ihY hw)) (ihY (ihX hw))
    apply hAll X
    · rw [lieSpan_simpleGenerators_eq_top]
      simp
    · exact hw

omit [FiniteDimensional ℂ V] in
/-- In an irreducible module, a nonzero generator-stable linear subspace is
the whole module. -/
theorem eq_top_of_simpleGeneratorStable
    [LieModule.IsIrreducible ℂ Algebra V]
    (W : Submodule ℂ V)
    (hStable : ∀ X ∈ simpleGenerators, ∀ {w : V}, w ∈ W → ⁅X, w⁆ ∈ W)
    (hW : W ≠ ⊥) :
    W = ⊤ := by
  let N := lieSubmoduleOfSimpleGeneratorStable W hStable
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hBot | hTop
  · exfalso
    apply hW
    have h := congrArg LieSubmodule.toSubmodule hBot
    simpa [N, lieSubmoduleOfSimpleGeneratorStable] using h
  · have h := congrArg LieSubmodule.toSubmodule hTop
    simpa [N, lieSubmoduleOfSimpleGeneratorStable] using h

/-- A single endomorphism whose real and imaginary eigenvalue parts record
both standard Cartan weights. -/
def cartanCombination : Module.End ℂ V :=
  toEnd ℂ Algebra V H1 + Complex.I • toEnd ℂ Algebra V H2

omit [FiniteDimensional ℂ V] in
theorem cartanCombination_apply_of_hasCartanWeight
    {w : V} {a b : ℂ} (P : HasCartanWeight w a b) :
    cartanCombination (V := V) w = (a + b * Complex.I) • w := by
  change ⁅H1, w⁆ + Complex.I • ⁅H2, w⁆ = _
  rw [P.lie_H1, P.lie_H2, smul_smul, ← add_smul]
  congr 1
  ring

omit [FiniteDimensional ℂ V] in
theorem rayVector_isEigenvector
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b)
    (i : RayIndex a b) :
    (cartanCombination (V := V)).HasEigenvector
      (encodeWeight (rayWeight a b i)) (rayVector v a b i) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    exact cartanCombination_apply_of_hasCartanWeight
      (rayVector_hasCartanWeight P i)
  · exact rayVector_ne_zero P i

omit [FiniteDimensional ℂ V] in
/-- All vectors on the three lowering rays are linearly independent.  The
proof uses the complex eigenvalue `x + i*y` to distinguish their two Cartan
weights. -/
theorem rayVector_linearIndependent
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b) :
    LinearIndependent ℂ (rayVector v a b) := by
  exact (cartanCombination (V := V)).eigenvectors_linearIndependent'
    (encodeWeight ∘ rayWeight a b)
    (encodeWeight_injective.comp (rayWeight_injective a b))
    (rayVector v a b) (rayVector_isEigenvector P)

/-- The three root strings alone force the lower bound
`2*a + 2*b + 1` on the representation dimension. -/
theorem two_mul_add_two_mul_add_one_le_finrank
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b) :
    2 * a + 2 * b + 1 ≤ Module.finrank ℂ V := by
  have h := (rayVector_linearIndependent P).fintype_card_le_finrank
  simp [RayIndex] at h
  omega

/-!
## Excluding the adjoint highest weight in dimension at most six
-/

/-- Seven weight vectors forced by a highest vector of weight `(1,1)`.  The
last two vectors move first in the composite-root direction and then in one
of the simple-root directions. -/
def adjointSevenVectors (v : V) : Fin 7 → V := ![
  v,
  lower F1 1 v,
  lower F2 1 v,
  lower F12 1 v,
  lower F12 2 v,
  lower F1 1 (lower F12 1 v),
  lower F2 1 (lower F12 1 v)]

def adjointSevenWeights : Fin 7 → ℤ × ℤ := ![
  (1, 1),
  (-1, 2),
  (2, -1),
  (0, 0),
  (-1, -1),
  (-2, 1),
  (1, -2)]

theorem adjointSevenWeights_injective :
    Function.Injective adjointSevenWeights := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [adjointSevenWeights] at h ⊢

omit [FiniteDimensional ℂ V] in
theorem adjointSevenVectors_hasCartanWeight
    {v : V} (P : HighestWeightVector v 1 1) (i : Fin 7) :
    HasCartanWeight (adjointSevenVectors v i)
      ((adjointSevenWeights i).1 : ℂ) ((adjointSevenWeights i).2 : ℂ) := by
  fin_cases i
  · simpa [adjointSevenVectors, adjointSevenWeights] using P.toHasCartanWeight
  · convert lower_F1_hasCartanWeight P.toHasCartanWeight 1 using 1 <;>
      norm_num [adjointSevenVectors, adjointSevenWeights]
  · convert lower_F2_hasCartanWeight P.toHasCartanWeight 1 using 1 <;>
      norm_num [adjointSevenVectors, adjointSevenWeights]
  · simpa [adjointSevenVectors, adjointSevenWeights] using
      lower_F12_hasCartanWeight P.toHasCartanWeight 1
  · convert lower_F12_hasCartanWeight P.toHasCartanWeight 2 using 1 <;>
      norm_num [adjointSevenVectors, adjointSevenWeights]
  · have hFirst := lower_F12_hasCartanWeight P.toHasCartanWeight 1
    simpa [adjointSevenVectors, adjointSevenWeights] using
      lower_F1_hasCartanWeight hFirst 1
  · have hFirst := lower_F12_hasCartanWeight P.toHasCartanWeight 1
    simpa [adjointSevenVectors, adjointSevenWeights] using
      lower_F2_hasCartanWeight hFirst 1

omit [FiniteDimensional ℂ V] in
private theorem lie_E1_lower_F12_one
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b) :
    ⁅E1, lower F12 1 v⁆ = -⁅F2, v⁆ := by
  rw [lower_succ, lower_zero, leibniz_lie, lie_E1_F12, P.lie_E1]
  simp

omit [FiniteDimensional ℂ V] in
private theorem lie_E2_lower_F12_one
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b) :
    ⁅E2, lower F12 1 v⁆ = ⁅F1, v⁆ := by
  rw [lower_succ, lower_zero, leibniz_lie, lie_E2_F12, P.lie_E2]
  simp

omit [FiniteDimensional ℂ V] in
private theorem lie_E1_lower_F1_one
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b) :
    ⁅E1, lower F1 1 v⁆ = (a : ℂ) • v := by
  rw [lower_succ, lower_zero, leibniz_lie, firstIsSl2Triple.lie_e_f,
    P.lie_E1, P.lie_H1]
  simp

omit [FiniteDimensional ℂ V] in
private theorem lie_E2_lower_F2_one
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b) :
    ⁅E2, lower F2 1 v⁆ = (b : ℂ) • v := by
  rw [lower_succ, lower_zero, leibniz_lie, secondIsSl2Triple.lie_e_f,
    P.lie_E2, P.lie_H2]
  simp

omit [FiniteDimensional ℂ V] in
private theorem firstMixed_raising
    {v : V} (P : HighestWeightVector v 1 1) :
    ⁅E1, ⁅E2, ⁅E1, lower F1 1 (lower F12 1 v)⁆⁆⁆ = -v := by
  have hWeight := lower_F12_hasCartanWeight P.toHasCartanWeight 1
  have hInner :
      ⁅E1, lower F1 1 (lower F12 1 v)⁆ = -⁅F1, ⁅F2, v⁆⁆ := by
    rw [lower_succ, lower_zero, leibniz_lie, firstIsSl2Triple.lie_e_f,
      hWeight.lie_H1, lie_E1_lower_F12_one P]
    simp
  have hE2F2 : ⁅E2, ⁅F2, v⁆⁆ = v := by
    simpa [lower_succ, lower_zero] using lie_E2_lower_F2_one P
  have hE1F1 : ⁅E1, ⁅F1, v⁆⁆ = v := by
    simpa [lower_succ, lower_zero] using lie_E1_lower_F1_one P
  rw [hInner, lie_neg, leibniz_lie, lie_E2_F1, zero_lie, zero_add, hE2F2,
    lie_neg, hE1F1]

omit [FiniteDimensional ℂ V] in
private theorem secondMixed_raising
    {v : V} (P : HighestWeightVector v 1 1) :
    ⁅E2, ⁅E1, ⁅E2, lower F2 1 (lower F12 1 v)⁆⁆⁆ = v := by
  have hWeight := lower_F12_hasCartanWeight P.toHasCartanWeight 1
  have hInner :
      ⁅E2, lower F2 1 (lower F12 1 v)⁆ = ⁅F2, ⁅F1, v⁆⁆ := by
    rw [lower_succ, lower_zero, leibniz_lie, secondIsSl2Triple.lie_e_f,
      hWeight.lie_H2, lie_E2_lower_F12_one P]
    simp
  have hE1F1 : ⁅E1, ⁅F1, v⁆⁆ = v := by
    simpa [lower_succ, lower_zero] using lie_E1_lower_F1_one P
  have hMiddle :
      ⁅E1, ⁅E2, lower F2 1 (lower F12 1 v)⁆⁆ = ⁅F2, v⁆ := by
    rw [hInner, leibniz_lie, lie_E1_F2, zero_lie, zero_add, hE1F1]
  have hE2F2 : ⁅E2, ⁅F2, v⁆⁆ = v := by
    simpa [lower_succ, lower_zero] using lie_E2_lower_F2_one P
  rw [hMiddle, hE2F2]

omit [FiniteDimensional ℂ V] in
theorem adjointSevenVectors_ne_zero
    {v : V} (P : HighestWeightVector v 1 1) (i : Fin 7) :
    adjointSevenVectors v i ≠ 0 := by
  fin_cases i
  · simpa [adjointSevenVectors] using P.ne_zero
  · simpa [adjointSevenVectors, lower] using
      P.firstPrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 1 ≤ 1)
  · simpa [adjointSevenVectors, lower] using
      P.secondPrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 1 ≤ 1)
  · simpa [adjointSevenVectors, lower] using
      P.compositePrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 1 ≤ 1 + 1)
  · simpa [adjointSevenVectors, lower] using
      P.compositePrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 2 ≤ 1 + 1)
  · intro hzero
    have h := firstMixed_raising P
    have hzero' : lower F1 1 (lower F12 1 v) = 0 := by
      simpa [adjointSevenVectors] using hzero
    rw [hzero', lie_zero, lie_zero, lie_zero] at h
    exact P.ne_zero (neg_eq_zero.mp h.symm)
  · intro hzero
    have h := secondMixed_raising P
    have hzero' : lower F2 1 (lower F12 1 v) = 0 := by
      simpa [adjointSevenVectors] using hzero
    rw [hzero', lie_zero, lie_zero, lie_zero] at h
    exact P.ne_zero h.symm

omit [FiniteDimensional ℂ V] in
theorem adjointSevenVectors_linearIndependent
    {v : V} (P : HighestWeightVector v 1 1) :
    LinearIndependent ℂ (adjointSevenVectors v) := by
  apply (cartanCombination (V := V)).eigenvectors_linearIndependent'
    (encodeWeight ∘ adjointSevenWeights)
    (encodeWeight_injective.comp adjointSevenWeights_injective)
    (adjointSevenVectors v)
  intro i
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    exact cartanCombination_apply_of_hasCartanWeight
      (adjointSevenVectors_hasCartanWeight P i)
  · exact adjointSevenVectors_ne_zero P i

/-- Highest weight `(1,1)` already forces at least seven dimensions. -/
theorem seven_le_finrank_of_one_one
    {v : V} (P : HighestWeightVector v 1 1) :
    7 ≤ Module.finrank ℂ V := by
  simpa using (adjointSevenVectors_linearIndependent P).fintype_card_le_finrank

/-!
## The two six-dimensional boundary weights
-/

def firstSymmetricSixVectors (v : V) : Fin 6 → V := ![
  v,
  lower F1 1 v,
  lower F1 2 v,
  lower F12 1 v,
  lower F12 2 v,
  lower F1 1 (lower F12 1 v)]

def firstSymmetricSixWeights : Fin 6 → ℤ × ℤ := ![
  (2, 0),
  (0, 1),
  (-2, 2),
  (1, -1),
  (0, -2),
  (-1, 0)]

theorem firstSymmetricSixWeights_injective :
    Function.Injective firstSymmetricSixWeights := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [firstSymmetricSixWeights] at h ⊢

omit [FiniteDimensional ℂ V] in
theorem firstSymmetricSixVectors_hasCartanWeight
    {v : V} (P : HighestWeightVector v 2 0) (i : Fin 6) :
    HasCartanWeight (firstSymmetricSixVectors v i)
      ((firstSymmetricSixWeights i).1 : ℂ)
      ((firstSymmetricSixWeights i).2 : ℂ) := by
  fin_cases i
  · simpa [firstSymmetricSixVectors, firstSymmetricSixWeights] using
      P.toHasCartanWeight
  · convert lower_F1_hasCartanWeight P.toHasCartanWeight 1 using 1 <;>
      norm_num [firstSymmetricSixVectors, firstSymmetricSixWeights]
  · convert lower_F1_hasCartanWeight P.toHasCartanWeight 2 using 1 <;>
      norm_num [firstSymmetricSixVectors, firstSymmetricSixWeights]
  · convert lower_F12_hasCartanWeight P.toHasCartanWeight 1 using 1 <;>
      norm_num [firstSymmetricSixVectors, firstSymmetricSixWeights]
  · convert lower_F12_hasCartanWeight P.toHasCartanWeight 2 using 1 <;>
      norm_num [firstSymmetricSixVectors, firstSymmetricSixWeights]
  · have hFirst := lower_F12_hasCartanWeight P.toHasCartanWeight 1
    convert lower_F1_hasCartanWeight hFirst 1 using 1 <;>
      norm_num [firstSymmetricSixVectors, firstSymmetricSixWeights]

omit [FiniteDimensional ℂ V] in
private theorem firstSymmetricMixed_raising
    {v : V} (P : HighestWeightVector v 2 0) :
    ⁅E2, lower F1 1 (lower F12 1 v)⁆ = lower F1 2 v := by
  have hOuter :
      lower F1 1 (lower F12 1 v) = ⁅F1, lower F12 1 v⁆ := by
    simpa using lower_succ F1 0 (lower F12 1 v)
  have hOne : lower F1 1 v = ⁅F1, v⁆ := by
    simpa using lower_succ F1 0 v
  have hTwo : lower F1 2 v = ⁅F1, lower F1 1 v⁆ := by
    simpa using lower_succ F1 1 v
  rw [hOuter, leibniz_lie E2 F1 (lower F12 1 v), lie_E2_F1,
    zero_lie, zero_add, lie_E2_lower_F12_one P, hTwo, hOne]

omit [FiniteDimensional ℂ V] in
theorem firstSymmetricSixVectors_ne_zero
    {v : V} (P : HighestWeightVector v 2 0) (i : Fin 6) :
    firstSymmetricSixVectors v i ≠ 0 := by
  fin_cases i
  · simpa [firstSymmetricSixVectors] using P.ne_zero
  · simpa [firstSymmetricSixVectors, lower] using
      P.firstPrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 1 ≤ 2)
  · simpa [firstSymmetricSixVectors, lower] using
      P.firstPrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 2 ≤ 2)
  · simpa [firstSymmetricSixVectors, lower] using
      P.compositePrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 1 ≤ 2 + 0)
  · simpa [firstSymmetricSixVectors, lower] using
      P.compositePrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 2 ≤ 2 + 0)
  · intro hzero
    have h := firstSymmetricMixed_raising P
    have hzero' : lower F1 1 (lower F12 1 v) = 0 := by
      simpa [firstSymmetricSixVectors] using hzero
    rw [hzero', lie_zero] at h
    have hn : lower F1 2 v ≠ 0 := by
      simpa [lower] using
        P.firstPrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 2 ≤ 2)
    exact hn h.symm

omit [FiniteDimensional ℂ V] in
theorem firstSymmetricSixVectors_linearIndependent
    {v : V} (P : HighestWeightVector v 2 0) :
    LinearIndependent ℂ (firstSymmetricSixVectors v) := by
  exact (cartanCombination (V := V)).eigenvectors_linearIndependent'
    (encodeWeight ∘ firstSymmetricSixWeights)
    (encodeWeight_injective.comp firstSymmetricSixWeights_injective)
    (firstSymmetricSixVectors v) (fun i ↦ by
      constructor
      · rw [Module.End.mem_eigenspace_iff]
        exact cartanCombination_apply_of_hasCartanWeight
          (firstSymmetricSixVectors_hasCartanWeight P i)
      · exact firstSymmetricSixVectors_ne_zero P i)

theorem six_le_finrank_of_two_zero
    {v : V} (P : HighestWeightVector v 2 0) :
    6 ≤ Module.finrank ℂ V := by
  simpa using
    (firstSymmetricSixVectors_linearIndependent P).fintype_card_le_finrank

def secondSymmetricSixVectors (v : V) : Fin 6 → V := ![
  v,
  lower F2 1 v,
  lower F2 2 v,
  lower F12 1 v,
  lower F12 2 v,
  lower F2 1 (lower F12 1 v)]

def secondSymmetricSixWeights : Fin 6 → ℤ × ℤ := ![
  (0, 2),
  (1, 0),
  (2, -2),
  (-1, 1),
  (-2, 0),
  (0, -1)]

theorem secondSymmetricSixWeights_injective :
    Function.Injective secondSymmetricSixWeights := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [secondSymmetricSixWeights] at h ⊢

omit [FiniteDimensional ℂ V] in
theorem secondSymmetricSixVectors_hasCartanWeight
    {v : V} (P : HighestWeightVector v 0 2) (i : Fin 6) :
    HasCartanWeight (secondSymmetricSixVectors v i)
      ((secondSymmetricSixWeights i).1 : ℂ)
      ((secondSymmetricSixWeights i).2 : ℂ) := by
  fin_cases i
  · simpa [secondSymmetricSixVectors, secondSymmetricSixWeights] using
      P.toHasCartanWeight
  · convert lower_F2_hasCartanWeight P.toHasCartanWeight 1 using 1 <;>
      norm_num [secondSymmetricSixVectors, secondSymmetricSixWeights]
  · convert lower_F2_hasCartanWeight P.toHasCartanWeight 2 using 1 <;>
      norm_num [secondSymmetricSixVectors, secondSymmetricSixWeights]
  · convert lower_F12_hasCartanWeight P.toHasCartanWeight 1 using 1 <;>
      norm_num [secondSymmetricSixVectors, secondSymmetricSixWeights]
  · convert lower_F12_hasCartanWeight P.toHasCartanWeight 2 using 1 <;>
      norm_num [secondSymmetricSixVectors, secondSymmetricSixWeights]
  · have hFirst := lower_F12_hasCartanWeight P.toHasCartanWeight 1
    convert lower_F2_hasCartanWeight hFirst 1 using 1 <;>
      norm_num [secondSymmetricSixVectors, secondSymmetricSixWeights]

omit [FiniteDimensional ℂ V] in
private theorem secondSymmetricMixed_raising
    {v : V} (P : HighestWeightVector v 0 2) :
    ⁅E1, lower F2 1 (lower F12 1 v)⁆ = -lower F2 2 v := by
  have hOuter :
      lower F2 1 (lower F12 1 v) = ⁅F2, lower F12 1 v⁆ := by
    simpa using lower_succ F2 0 (lower F12 1 v)
  have hOne : lower F2 1 v = ⁅F2, v⁆ := by
    simpa using lower_succ F2 0 v
  have hTwo : lower F2 2 v = ⁅F2, lower F2 1 v⁆ := by
    simpa using lower_succ F2 1 v
  rw [hOuter, leibniz_lie E1 F2 (lower F12 1 v), lie_E1_F2,
    zero_lie, zero_add, lie_E1_lower_F12_one P, lie_neg, hTwo, hOne]

omit [FiniteDimensional ℂ V] in
theorem secondSymmetricSixVectors_ne_zero
    {v : V} (P : HighestWeightVector v 0 2) (i : Fin 6) :
    secondSymmetricSixVectors v i ≠ 0 := by
  fin_cases i
  · simpa [secondSymmetricSixVectors] using P.ne_zero
  · simpa [secondSymmetricSixVectors, lower] using
      P.secondPrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 1 ≤ 2)
  · simpa [secondSymmetricSixVectors, lower] using
      P.secondPrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 2 ≤ 2)
  · simpa [secondSymmetricSixVectors, lower] using
      P.compositePrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 1 ≤ 0 + 2)
  · simpa [secondSymmetricSixVectors, lower] using
      P.compositePrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 2 ≤ 0 + 2)
  · intro hzero
    have h := secondSymmetricMixed_raising P
    have hzero' : lower F2 1 (lower F12 1 v) = 0 := by
      simpa [secondSymmetricSixVectors] using hzero
    rw [hzero', lie_zero] at h
    apply (by
      simpa [lower] using
        P.secondPrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega : 2 ≤ 2))
    exact neg_eq_zero.mp h.symm

omit [FiniteDimensional ℂ V] in
theorem secondSymmetricSixVectors_linearIndependent
    {v : V} (P : HighestWeightVector v 0 2) :
    LinearIndependent ℂ (secondSymmetricSixVectors v) := by
  exact (cartanCombination (V := V)).eigenvectors_linearIndependent'
    (encodeWeight ∘ secondSymmetricSixWeights)
    (encodeWeight_injective.comp secondSymmetricSixWeights_injective)
    (secondSymmetricSixVectors v) (fun i ↦ by
      constructor
      · rw [Module.End.mem_eigenspace_iff]
        exact cartanCombination_apply_of_hasCartanWeight
          (secondSymmetricSixVectors_hasCartanWeight P i)
      · exact secondSymmetricSixVectors_ne_zero P i)

theorem six_le_finrank_of_zero_two
    {v : V} (P : HighestWeightVector v 0 2) :
    6 ≤ Module.finrank ℂ V := by
  simpa using
    (secondSymmetricSixVectors_linearIndependent P).fintype_card_le_finrank

/-!
## Classification in dimension at most six
-/

/-- The lowering rays and the exceptional `(1,1)` calculation leave exactly
five possible dominant highest weights in dimension at most six. -/
theorem highestWeight_candidates_of_finrank_le_six
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b)
    (hDimension : Module.finrank ℂ V ≤ 6) :
    (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨
      (a = 2 ∧ b = 0) ∨ (a = 0 ∧ b = 2) := by
  have hRays := two_mul_add_two_mul_add_one_le_finrank P
  have hSum : a + b ≤ 2 := by omega
  by_cases hAdjoint : a = 1 ∧ b = 1
  · rcases hAdjoint with ⟨rfl, rfl⟩
    have hSeven := seven_le_finrank_of_one_one P
    omega
  · omega

private def trivialHighestSpan (v : V) : Submodule ℂ V :=
  Submodule.span ℂ {v}

private theorem trivialHighestSpan_simpleGeneratorStable
    {v : V} (P : HighestWeightVector v 0 0) :
    ∀ X ∈ simpleGenerators, ∀ {w : V}, w ∈ trivialHighestSpan v →
      ⁅X, w⁆ ∈ trivialHighestSpan v := by
  have hF1 : ⁅F1, v⁆ = 0 := by
    have h := lower_F1_highestWeight_add_one_eq_zero P
    simpa [lower_succ, lower_zero] using h
  have hF2 : ⁅F2, v⁆ = 0 := by
    have h := lower_F2_highestWeight_add_one_eq_zero P
    simpa [lower_succ, lower_zero] using h
  intro X hX w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      simp only [Set.mem_singleton_iff] at hw
      subst w
      simp only [simpleGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [P.lie_H1]
        simp [trivialHighestSpan]
      · rw [P.lie_H2]
        simp [trivialHighestSpan]
      · rw [P.lie_E1]
        exact (trivialHighestSpan v).zero_mem
      · rw [hF1]
        exact (trivialHighestSpan v).zero_mem
      · rw [P.lie_E2]
        exact (trivialHighestSpan v).zero_mem
      · rw [hF2]
        exact (trivialHighestSpan v).zero_mem
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [lie_add]
      exact (trivialHighestSpan v).add_mem ihx ihy
  | smul c x hx ihx =>
      rw [lie_smul]
      exact (trivialHighestSpan v).smul_mem c ihx

theorem trivialHighestSpan_eq_top
    [LieModule.IsIrreducible ℂ Algebra V]
    {v : V} (P : HighestWeightVector v 0 0) :
    trivialHighestSpan v = ⊤ := by
  apply eq_top_of_simpleGeneratorStable
    (trivialHighestSpan v) (trivialHighestSpan_simpleGeneratorStable P)
  intro hBot
  apply P.ne_zero
  have hv : v ∈ trivialHighestSpan v := by
    exact Submodule.subset_span (by simp)
  rw [hBot] at hv
  exact hv

theorem finrank_eq_one_of_highestWeight_zero_zero
    [LieModule.IsIrreducible ℂ Algebra V]
    {v : V} (P : HighestWeightVector v 0 0) :
    Module.finrank ℂ V = 1 := by
  have hSpan := trivialHighestSpan_eq_top P
  have hLine := finrank_span_singleton (K := ℂ) P.ne_zero
  have hSpan' : Submodule.span ℂ {v} = ⊤ := by
    simpa [trivialHighestSpan] using hSpan
  rw [hSpan', finrank_top] at hLine
  exact hLine

/-! The two fundamental highest weights. -/

def firstFundamentalVectors (v : V) : Fin 3 → V := ![
  v,
  lower F1 1 v,
  lower F12 1 v]

def firstFundamentalWeights : Fin 3 → ℤ × ℤ := ![
  (1, 0),
  (-1, 1),
  (0, -1)]

private def firstFundamentalSpan (v : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range (firstFundamentalVectors v))

omit [FiniteDimensional ℂ V] in
theorem firstFundamentalVectors_hasCartanWeight
    {v : V} (P : HighestWeightVector v 1 0) (i : Fin 3) :
    HasCartanWeight (firstFundamentalVectors v i)
      ((firstFundamentalWeights i).1 : ℂ)
      ((firstFundamentalWeights i).2 : ℂ) := by
  fin_cases i
  · simpa [firstFundamentalVectors, firstFundamentalWeights] using
      P.toHasCartanWeight
  · convert lower_F1_hasCartanWeight P.toHasCartanWeight 1 using 1 <;>
      norm_num [firstFundamentalVectors, firstFundamentalWeights]
  · convert lower_F12_hasCartanWeight P.toHasCartanWeight 1 using 1 <;>
      norm_num [firstFundamentalVectors, firstFundamentalWeights]

omit [FiniteDimensional ℂ V] in
private theorem firstFundamentalVector_mem
    (v : V) (i : Fin 3) :
    firstFundamentalVectors v i ∈ firstFundamentalSpan v :=
  Submodule.subset_span ⟨i, rfl⟩

private theorem firstFundamental_lie_F2_v
    {v : V} (P : HighestWeightVector v 1 0) :
    ⁅F2, v⁆ = 0 := by
  have h := lower_F2_highestWeight_add_one_eq_zero P
  simpa [lower_succ, lower_zero] using h

private theorem firstFundamental_lie_F1_F1_v
    {v : V} (P : HighestWeightVector v 1 0) :
    ⁅F1, lower F1 1 v⁆ = 0 := by
  have h := lower_F1_highestWeight_add_one_eq_zero P
  simpa [lower_succ, lower_zero] using h

private theorem firstFundamental_lie_F1_F12_v
    {v : V} (P : HighestWeightVector v 1 0) :
    ⁅F1, lower F12 1 v⁆ = 0 := by
  have hWeight := lower_F12_hasCartanWeight P.toHasCartanWeight 1
  have hPrimitive :
      firstIsSl2Triple.HasPrimitiveVectorWith (lower F12 1 v) (0 : ℂ) :=
    { ne_zero := by
        simpa [lower] using
          P.compositePrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl
            (by omega : 1 ≤ 1 + 0)
      lie_h := by
        convert hWeight.lie_H1 using 1 ; norm_num
      lie_e := by
        rw [lie_E1_lower_F12_one P, firstFundamental_lie_F2_v P]
        simp }
  have h := hPrimitive.pow_toEnd_f_eq_zero_of_eq_nat (R := ℂ) (n := 0)
    (by norm_num)
  simpa [lower, lower_succ, lower_zero] using h

private theorem firstFundamental_lie_F2_F12_v
    {v : V} (P : HighestWeightVector v 1 0) :
    ⁅F2, lower F12 1 v⁆ = 0 := by
  have hOne : lower F12 1 v = ⁅F12, v⁆ := by
    simpa using lower_succ F12 0 v
  rw [hOne, leibniz_lie F2 F12 v, lie_F2_F12,
    firstFundamental_lie_F2_v P]
  simp

private theorem firstFundamental_lie_F2_F1_v
    {v : V} (P : HighestWeightVector v 1 0) :
    ⁅F2, lower F1 1 v⁆ = lower F12 1 v := by
  have hF1 : lower F1 1 v = ⁅F1, v⁆ := by
    simpa using lower_succ F1 0 v
  have hF12 : lower F12 1 v = ⁅F12, v⁆ := by
    simpa using lower_succ F12 0 v
  rw [hF1, hF12, leibniz_lie F2 F1 v, lie_F2_F1,
    firstFundamental_lie_F2_v P, lie_zero, add_zero]

omit [FiniteDimensional ℂ V] in
private theorem firstFundamental_lie_H1_mem
    {v : V} (P : HighestWeightVector v 1 0) (i : Fin 3) :
    ⁅H1, firstFundamentalVectors v i⁆ ∈ firstFundamentalSpan v := by
  rw [(firstFundamentalVectors_hasCartanWeight P i).lie_H1]
  exact (firstFundamentalSpan v).smul_mem _ (firstFundamentalVector_mem v i)

omit [FiniteDimensional ℂ V] in
private theorem firstFundamental_lie_H2_mem
    {v : V} (P : HighestWeightVector v 1 0) (i : Fin 3) :
    ⁅H2, firstFundamentalVectors v i⁆ ∈ firstFundamentalSpan v := by
  rw [(firstFundamentalVectors_hasCartanWeight P i).lie_H2]
  exact (firstFundamentalSpan v).smul_mem _ (firstFundamentalVector_mem v i)

private theorem firstFundamental_lie_E1_mem
    {v : V} (P : HighestWeightVector v 1 0) (i : Fin 3) :
    ⁅E1, firstFundamentalVectors v i⁆ ∈ firstFundamentalSpan v := by
  fin_cases i
  · change ⁅E1, v⁆ ∈ firstFundamentalSpan v
    rw [P.lie_E1]
    exact (firstFundamentalSpan v).zero_mem
  · change ⁅E1, lower F1 1 v⁆ ∈ firstFundamentalSpan v
    rw [lie_E1_lower_F1_one P]
    simpa [firstFundamentalVectors] using firstFundamentalVector_mem v 0
  · change ⁅E1, lower F12 1 v⁆ ∈ firstFundamentalSpan v
    rw [lie_E1_lower_F12_one P, firstFundamental_lie_F2_v P]
    simp

omit [FiniteDimensional ℂ V] in
private theorem firstFundamental_lie_E2_mem
    {v : V} (P : HighestWeightVector v 1 0) (i : Fin 3) :
    ⁅E2, firstFundamentalVectors v i⁆ ∈ firstFundamentalSpan v := by
  fin_cases i
  · change ⁅E2, v⁆ ∈ firstFundamentalSpan v
    rw [P.lie_E2]
    exact (firstFundamentalSpan v).zero_mem
  · have hOne : lower F1 1 v = ⁅F1, v⁆ := by
      simpa using lower_succ F1 0 v
    change ⁅E2, lower F1 1 v⁆ ∈ firstFundamentalSpan v
    rw [hOne, leibniz_lie E2 F1 v, lie_E2_F1, P.lie_E2]
    simp [firstFundamentalSpan]
  · change ⁅E2, lower F12 1 v⁆ ∈ firstFundamentalSpan v
    rw [lie_E2_lower_F12_one P]
    have hOne : ⁅F1, v⁆ = lower F1 1 v := by
      simpa using (lower_succ F1 0 v).symm
    rw [hOne]
    exact firstFundamentalVector_mem v 1

private theorem firstFundamental_lie_F1_mem
    {v : V} (P : HighestWeightVector v 1 0) (i : Fin 3) :
    ⁅F1, firstFundamentalVectors v i⁆ ∈ firstFundamentalSpan v := by
  fin_cases i
  · have hOne : ⁅F1, v⁆ = lower F1 1 v := by
      simpa using (lower_succ F1 0 v).symm
    change ⁅F1, v⁆ ∈ firstFundamentalSpan v
    rw [hOne]
    exact firstFundamentalVector_mem v 1
  · change ⁅F1, lower F1 1 v⁆ ∈ firstFundamentalSpan v
    rw [firstFundamental_lie_F1_F1_v P]
    exact (firstFundamentalSpan v).zero_mem
  · change ⁅F1, lower F12 1 v⁆ ∈ firstFundamentalSpan v
    rw [firstFundamental_lie_F1_F12_v P]
    exact (firstFundamentalSpan v).zero_mem

private theorem firstFundamental_lie_F2_mem
    {v : V} (P : HighestWeightVector v 1 0) (i : Fin 3) :
    ⁅F2, firstFundamentalVectors v i⁆ ∈ firstFundamentalSpan v := by
  fin_cases i
  · change ⁅F2, v⁆ ∈ firstFundamentalSpan v
    rw [firstFundamental_lie_F2_v P]
    exact (firstFundamentalSpan v).zero_mem
  · change ⁅F2, lower F1 1 v⁆ ∈ firstFundamentalSpan v
    rw [firstFundamental_lie_F2_F1_v P]
    exact firstFundamentalVector_mem v 2
  · change ⁅F2, lower F12 1 v⁆ ∈ firstFundamentalSpan v
    rw [firstFundamental_lie_F2_F12_v P]
    exact (firstFundamentalSpan v).zero_mem

private theorem firstFundamentalSpan_simpleGeneratorStable
    {v : V} (P : HighestWeightVector v 1 0) :
    ∀ X ∈ simpleGenerators, ∀ {w : V}, w ∈ firstFundamentalSpan v →
      ⁅X, w⁆ ∈ firstFundamentalSpan v := by
  intro X hX w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      simp only [simpleGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
      · exact firstFundamental_lie_H1_mem P i
      · exact firstFundamental_lie_H2_mem P i
      · exact firstFundamental_lie_E1_mem P i
      · exact firstFundamental_lie_F1_mem P i
      · exact firstFundamental_lie_E2_mem P i
      · exact firstFundamental_lie_F2_mem P i
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [lie_add]
      exact (firstFundamentalSpan v).add_mem ihx ihy
  | smul c x hx ihx =>
      rw [lie_smul]
      exact (firstFundamentalSpan v).smul_mem c ihx

theorem firstFundamentalSpan_eq_top
    [LieModule.IsIrreducible ℂ Algebra V]
    {v : V} (P : HighestWeightVector v 1 0) :
    firstFundamentalSpan v = ⊤ := by
  apply eq_top_of_simpleGeneratorStable
    (firstFundamentalSpan v) (firstFundamentalSpan_simpleGeneratorStable P)
  intro hBot
  apply P.ne_zero
  have hv := firstFundamentalVector_mem v 0
  rw [hBot] at hv
  exact hv

theorem finrank_eq_three_of_highestWeight_one_zero
    [LieModule.IsIrreducible ℂ Algebra V]
    {v : V} (P : HighestWeightVector v 1 0) :
    Module.finrank ℂ V = 3 := by
  have hUpper : Module.finrank ℂ V ≤ 3 := by
    simpa using finrank_le_of_span_eq_top (R := ℂ)
      (firstFundamentalSpan_eq_top P)
  have hLower := two_mul_add_two_mul_add_one_le_finrank P
  omega

def secondFundamentalVectors (v : V) : Fin 3 → V := ![
  v,
  lower F2 1 v,
  lower F12 1 v]

def secondFundamentalWeights : Fin 3 → ℤ × ℤ := ![
  (0, 1),
  (1, -1),
  (-1, 0)]

private def secondFundamentalSpan (v : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range (secondFundamentalVectors v))

omit [FiniteDimensional ℂ V] in
theorem secondFundamentalVectors_hasCartanWeight
    {v : V} (P : HighestWeightVector v 0 1) (i : Fin 3) :
    HasCartanWeight (secondFundamentalVectors v i)
      ((secondFundamentalWeights i).1 : ℂ)
      ((secondFundamentalWeights i).2 : ℂ) := by
  fin_cases i
  · simpa [secondFundamentalVectors, secondFundamentalWeights] using
      P.toHasCartanWeight
  · convert lower_F2_hasCartanWeight P.toHasCartanWeight 1 using 1 <;>
      norm_num [secondFundamentalVectors, secondFundamentalWeights]
  · convert lower_F12_hasCartanWeight P.toHasCartanWeight 1 using 1 <;>
      norm_num [secondFundamentalVectors, secondFundamentalWeights]

omit [FiniteDimensional ℂ V] in
private theorem secondFundamentalVector_mem
    (v : V) (i : Fin 3) :
    secondFundamentalVectors v i ∈ secondFundamentalSpan v :=
  Submodule.subset_span ⟨i, rfl⟩

private theorem secondFundamental_lie_F1_v
    {v : V} (P : HighestWeightVector v 0 1) :
    ⁅F1, v⁆ = 0 := by
  have h := lower_F1_highestWeight_add_one_eq_zero P
  simpa [lower_succ, lower_zero] using h

private theorem secondFundamental_lie_F2_F2_v
    {v : V} (P : HighestWeightVector v 0 1) :
    ⁅F2, lower F2 1 v⁆ = 0 := by
  have h := lower_F2_highestWeight_add_one_eq_zero P
  simpa [lower_succ, lower_zero] using h

private theorem secondFundamental_lie_F2_F12_v
    {v : V} (P : HighestWeightVector v 0 1) :
    ⁅F2, lower F12 1 v⁆ = 0 := by
  have hWeight := lower_F12_hasCartanWeight P.toHasCartanWeight 1
  have hPrimitive :
      secondIsSl2Triple.HasPrimitiveVectorWith (lower F12 1 v) (0 : ℂ) :=
    { ne_zero := by
        simpa [lower] using
          P.compositePrimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl
            (by omega : 1 ≤ 0 + 1)
      lie_h := by
        convert hWeight.lie_H2 using 1 ; norm_num
      lie_e := by
        rw [lie_E2_lower_F12_one P, secondFundamental_lie_F1_v P] }
  have h := hPrimitive.pow_toEnd_f_eq_zero_of_eq_nat (R := ℂ) (n := 0)
    (by norm_num)
  simpa [lower, lower_succ, lower_zero] using h

private theorem secondFundamental_lie_F1_F12_v
    {v : V} (P : HighestWeightVector v 0 1) :
    ⁅F1, lower F12 1 v⁆ = 0 := by
  have hOne : lower F12 1 v = ⁅F12, v⁆ := by
    simpa using lower_succ F12 0 v
  rw [hOne, leibniz_lie F1 F12 v, lie_F1_F12,
    secondFundamental_lie_F1_v P]
  simp

private theorem secondFundamental_lie_F1_F2_v
    {v : V} (P : HighestWeightVector v 0 1) :
    ⁅F1, lower F2 1 v⁆ = -lower F12 1 v := by
  have hF2 : lower F2 1 v = ⁅F2, v⁆ := by
    simpa using lower_succ F2 0 v
  have hF12 : lower F12 1 v = ⁅F12, v⁆ := by
    simpa using lower_succ F12 0 v
  have hBracket : ⁅F1, F2⁆ = -F12 := by
    calc
      ⁅F1, F2⁆ = -⁅F2, F1⁆ := (lie_skew (x := F1) (y := F2)).symm
      _ = -F12 := congrArg Neg.neg lie_F2_F1
  rw [hF2, hF12, leibniz_lie F1 F2 v, hBracket, neg_lie,
    secondFundamental_lie_F1_v P, lie_zero, add_zero]

omit [FiniteDimensional ℂ V] in
private theorem secondFundamental_lie_H1_mem
    {v : V} (P : HighestWeightVector v 0 1) (i : Fin 3) :
    ⁅H1, secondFundamentalVectors v i⁆ ∈ secondFundamentalSpan v := by
  rw [(secondFundamentalVectors_hasCartanWeight P i).lie_H1]
  exact (secondFundamentalSpan v).smul_mem _ (secondFundamentalVector_mem v i)

omit [FiniteDimensional ℂ V] in
private theorem secondFundamental_lie_H2_mem
    {v : V} (P : HighestWeightVector v 0 1) (i : Fin 3) :
    ⁅H2, secondFundamentalVectors v i⁆ ∈ secondFundamentalSpan v := by
  rw [(secondFundamentalVectors_hasCartanWeight P i).lie_H2]
  exact (secondFundamentalSpan v).smul_mem _ (secondFundamentalVector_mem v i)

omit [FiniteDimensional ℂ V] in
private theorem secondFundamental_lie_E1_mem
    {v : V} (P : HighestWeightVector v 0 1) (i : Fin 3) :
    ⁅E1, secondFundamentalVectors v i⁆ ∈ secondFundamentalSpan v := by
  fin_cases i
  · change ⁅E1, v⁆ ∈ secondFundamentalSpan v
    rw [P.lie_E1]
    exact (secondFundamentalSpan v).zero_mem
  · have hOne : lower F2 1 v = ⁅F2, v⁆ := by
      simpa using lower_succ F2 0 v
    change ⁅E1, lower F2 1 v⁆ ∈ secondFundamentalSpan v
    rw [hOne, leibniz_lie E1 F2 v, lie_E1_F2, P.lie_E1]
    simp [secondFundamentalSpan]
  · change ⁅E1, lower F12 1 v⁆ ∈ secondFundamentalSpan v
    rw [lie_E1_lower_F12_one P]
    have hBase : ⁅F2, v⁆ = lower F2 1 v := by
      simpa using (lower_succ F2 0 v).symm
    have hOne : -⁅F2, v⁆ = -lower F2 1 v := congrArg Neg.neg hBase
    rw [hOne]
    exact (secondFundamentalSpan v).neg_mem (secondFundamentalVector_mem v 1)

private theorem secondFundamental_lie_E2_mem
    {v : V} (P : HighestWeightVector v 0 1) (i : Fin 3) :
    ⁅E2, secondFundamentalVectors v i⁆ ∈ secondFundamentalSpan v := by
  fin_cases i
  · change ⁅E2, v⁆ ∈ secondFundamentalSpan v
    rw [P.lie_E2]
    exact (secondFundamentalSpan v).zero_mem
  · change ⁅E2, lower F2 1 v⁆ ∈ secondFundamentalSpan v
    rw [lie_E2_lower_F2_one P]
    simpa [secondFundamentalVectors] using secondFundamentalVector_mem v 0
  · change ⁅E2, lower F12 1 v⁆ ∈ secondFundamentalSpan v
    rw [lie_E2_lower_F12_one P, secondFundamental_lie_F1_v P]
    exact (secondFundamentalSpan v).zero_mem

private theorem secondFundamental_lie_F1_mem
    {v : V} (P : HighestWeightVector v 0 1) (i : Fin 3) :
    ⁅F1, secondFundamentalVectors v i⁆ ∈ secondFundamentalSpan v := by
  fin_cases i
  · change ⁅F1, v⁆ ∈ secondFundamentalSpan v
    rw [secondFundamental_lie_F1_v P]
    exact (secondFundamentalSpan v).zero_mem
  · change ⁅F1, lower F2 1 v⁆ ∈ secondFundamentalSpan v
    rw [secondFundamental_lie_F1_F2_v P]
    exact (secondFundamentalSpan v).neg_mem (secondFundamentalVector_mem v 2)
  · change ⁅F1, lower F12 1 v⁆ ∈ secondFundamentalSpan v
    rw [secondFundamental_lie_F1_F12_v P]
    exact (secondFundamentalSpan v).zero_mem

private theorem secondFundamental_lie_F2_mem
    {v : V} (P : HighestWeightVector v 0 1) (i : Fin 3) :
    ⁅F2, secondFundamentalVectors v i⁆ ∈ secondFundamentalSpan v := by
  fin_cases i
  · have hOne : ⁅F2, v⁆ = lower F2 1 v := by
      simpa using (lower_succ F2 0 v).symm
    change ⁅F2, v⁆ ∈ secondFundamentalSpan v
    rw [hOne]
    exact secondFundamentalVector_mem v 1
  · change ⁅F2, lower F2 1 v⁆ ∈ secondFundamentalSpan v
    rw [secondFundamental_lie_F2_F2_v P]
    exact (secondFundamentalSpan v).zero_mem
  · change ⁅F2, lower F12 1 v⁆ ∈ secondFundamentalSpan v
    rw [secondFundamental_lie_F2_F12_v P]
    exact (secondFundamentalSpan v).zero_mem

private theorem secondFundamentalSpan_simpleGeneratorStable
    {v : V} (P : HighestWeightVector v 0 1) :
    ∀ X ∈ simpleGenerators, ∀ {w : V}, w ∈ secondFundamentalSpan v →
      ⁅X, w⁆ ∈ secondFundamentalSpan v := by
  intro X hX w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      simp only [simpleGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
      · exact secondFundamental_lie_H1_mem P i
      · exact secondFundamental_lie_H2_mem P i
      · exact secondFundamental_lie_E1_mem P i
      · exact secondFundamental_lie_F1_mem P i
      · exact secondFundamental_lie_E2_mem P i
      · exact secondFundamental_lie_F2_mem P i
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [lie_add]
      exact (secondFundamentalSpan v).add_mem ihx ihy
  | smul c x hx ihx =>
      rw [lie_smul]
      exact (secondFundamentalSpan v).smul_mem c ihx

theorem secondFundamentalSpan_eq_top
    [LieModule.IsIrreducible ℂ Algebra V]
    {v : V} (P : HighestWeightVector v 0 1) :
    secondFundamentalSpan v = ⊤ := by
  apply eq_top_of_simpleGeneratorStable
    (secondFundamentalSpan v) (secondFundamentalSpan_simpleGeneratorStable P)
  intro hBot
  apply P.ne_zero
  have hv := secondFundamentalVector_mem v 0
  rw [hBot] at hv
  exact hv

theorem finrank_eq_three_of_highestWeight_zero_one
    [LieModule.IsIrreducible ℂ Algebra V]
    {v : V} (P : HighestWeightVector v 0 1) :
    Module.finrank ℂ V = 3 := by
  have hUpper : Module.finrank ℂ V ≤ 3 := by
    simpa using finrank_le_of_span_eq_top (R := ℂ)
      (secondFundamentalSpan_eq_top P)
  have hLower := two_mul_add_two_mul_add_one_le_finrank P
  omega

theorem finrank_eq_six_of_highestWeight_two_zero
    {v : V} (P : HighestWeightVector v 2 0)
    (hDimension : Module.finrank ℂ V ≤ 6) :
    Module.finrank ℂ V = 6 := by
  have hLower := six_le_finrank_of_two_zero P
  omega

theorem finrank_eq_six_of_highestWeight_zero_two
    {v : V} (P : HighestWeightVector v 0 2)
    (hDimension : Module.finrank ℂ V ≤ 6) :
    Module.finrank ℂ V = 6 := by
  have hLower := six_le_finrank_of_zero_two P
  omega

/-- An irreducible finite-dimensional `sl₃(ℂ)` module of dimension at most
six, once equipped with a dominant integral highest vector, has dimension
`1`, `3`, or `6`. -/
theorem finrank_eq_one_or_three_or_six_of_highestWeight
    [LieModule.IsIrreducible ℂ Algebra V]
    {v : V} {a b : ℕ} (P : HighestWeightVector v a b)
    (hDimension : Module.finrank ℂ V ≤ 6) :
    Module.finrank ℂ V = 1 ∨ Module.finrank ℂ V = 3 ∨
      Module.finrank ℂ V = 6 := by
  rcases highestWeight_candidates_of_finrank_le_six P hDimension with
    h00 | h10 | h01 | h20 | h02
  · rcases h00 with ⟨rfl, rfl⟩
    exact Or.inl (finrank_eq_one_of_highestWeight_zero_zero P)
  · rcases h10 with ⟨rfl, rfl⟩
    exact Or.inr (Or.inl (finrank_eq_three_of_highestWeight_one_zero P))
  · rcases h01 with ⟨rfl, rfl⟩
    exact Or.inr (Or.inl (finrank_eq_three_of_highestWeight_zero_one P))
  · rcases h20 with ⟨rfl, rfl⟩
    exact Or.inr (Or.inr (finrank_eq_six_of_highestWeight_two_zero P hDimension))
  · rcases h02 with ⟨rfl, rfl⟩
    exact Or.inr (Or.inr (finrank_eq_six_of_highestWeight_zero_two P hDimension))

end

end Sl3HighestWeight
end Math
