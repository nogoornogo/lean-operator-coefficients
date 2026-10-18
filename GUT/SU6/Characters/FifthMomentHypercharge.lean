import GUT.SU6.Hypercharge.HyperchargeBranchArithmetic
import GUT.SU6.Characters.DegreeFiveWeylInvariant
import GUT.SU6.Characters.AmbientWeylMoment
import Mathlib.Tactic

/-!
# Fifth-moment classification of the hypercharge cocharacter

For a Cartan element of `su(3) + su(2) + u(1)` write the two independent
color entries as `a,b`, the weak entry as `t`, and the hypercharge parameter
as `h`.  A centralizer cocharacter `(m,n)` embeds it into the trace-zero
six-dimensional Cartan with entries

`a+mh, b+mh, -a-b+mh, t+nh, -t+nh, -(3m+2n)h`.

The degree-five Weyl invariants on the trace-zero `SU(6)` Cartan are spanned
by `p5` and `p2*p3`.  This file proves the complete arithmetic consequence
of that invariant-theory statement: the fifth weight moment of one Standard
Model generation can be the restriction of `A*p5+B*p2*p3` only for the
standard pair `(-2,3)`.  The proof uses exact rational evaluations, not a
bounded search.

`PhysicalFifthMomentBridge` supplies the representation-theory source from an
exact finite physical-weight restriction of an actual virtual `SU(6)` Laurent
character.  This file keeps the invariant-theory and arithmetic core separate.
-/

namespace GUT
namespace FifthMomentHypercharge

open HyperchargeBranchArithmetic

/-- The restriction of the `k`-th power sum on the trace-zero `SU(6)` Cartan
along the centralizer cocharacter `(m,n)`. -/
def ambientPowerSum (k : ℕ) (m n a b t h : ℚ) : ℚ :=
  (a + m * h) ^ k + (b + m * h) ^ k + (-a - b + m * h) ^ k +
    (t + n * h) ^ k + (-t + n * h) ^ k + ((-3 * m - 2 * n) * h) ^ k

/-- The six trace-zero Cartan coordinates induced by the physical
`SU(3) x SU(2) x U(1)` Cartan and centralizer cocharacter `(m,n)`. -/
def ambientCartanCoordinates (m n a b t h : ℚ) : Fin 6 → ℚ :=
  ![a + m * h, b + m * h, -a - b + m * h,
    t + n * h, -t + n * h, (-3 * m - 2 * n) * h]

theorem ambientCartanCoordinates_sum (m n a b t h : ℚ) :
    ∑ i, ambientCartanCoordinates m n a b t h i = 0 := by
  simp [ambientCartanCoordinates, Fin.sum_univ_succ]
  ring

theorem powerSumValue_ambientCartanCoordinates
    (k : ℕ) (m n a b t h : ℚ) :
    DegreeFiveWeylInvariant.powerSumValue
        (ambientCartanCoordinates m n a b t h) k =
      ambientPowerSum k m n a b t h := by
  simp [DegreeFiveWeylInvariant.powerSumValue, ambientCartanCoordinates,
    ambientPowerSum, Fin.sum_univ_succ]
  ring

/-- The normalized fifth weight moment of the five left-handed multiplets
`Q, u^c, d^c, L, e^c` in one Standard Model generation.  The fifth moment of
the corresponding character-minus-dual is twice this polynomial, an
irrelevant nonzero scalar for the classification. -/
def smFifthMoment (a b t h : ℚ) : ℚ :=
  (a + t + h) ^ 5 + (a - t + h) ^ 5 +
  (b + t + h) ^ 5 + (b - t + h) ^ 5 +
  (-a - b + t + h) ^ 5 + (-a - b - t + h) ^ 5 +
  (-a - 4 * h) ^ 5 + (-b - 4 * h) ^ 5 +
  (a + b - 4 * h) ^ 5 +
  (-a + 2 * h) ^ 5 + (-b + 2 * h) ^ 5 +
  (a + b + 2 * h) ^ 5 +
  (t - 3 * h) ^ 5 + (-t - 3 * h) ^ 5 + (6 * h) ^ 5

/-- A general degree-five `SU(6)` Weyl invariant after restriction to the
physical Cartan. -/
def restrictedDegreeFiveInvariant
    (m n A B a b t h : ℚ) : ℚ :=
  A * ambientPowerSum 5 m n a b t h +
    B * ambientPowerSum 2 m n a b t h * ambientPowerSum 3 m n a b t h

/-- The exact invariant-theory output needed from a putative `SU(6)` source
character at degree five. -/
def HasFifthMomentExtension (m n : ℚ) : Prop :=
  ∃ A B : ℚ, ∀ a b t h : ℚ,
    smFifthMoment a b t h = restrictedDegreeFiveInvariant m n A B a b t h

/-- A representation-theoretic fifth moment has been supplied as a symmetric
homogeneous degree-five polynomial on the ambient six-coordinate Cartan. -/
def HasWeylInvariantFifthMomentSource (m n : ℚ) : Prop :=
  ∃ p : MvPolynomial (Fin 6) ℚ,
    p.IsSymmetric ∧ p.IsHomogeneous 5 ∧
      ∀ a b t h : ℚ,
        smFifthMoment a b t h =
          MvPolynomial.eval (ambientCartanCoordinates m n a b t h) p

/-- The same source condition with an arbitrary rational multiplicity, used
for a nonzero number of identical chiral generations. -/
def HasScaledWeylInvariantFifthMomentSource
    (generations m n : ℚ) : Prop :=
  ∃ p : MvPolynomial (Fin 6) ℚ,
    p.IsSymmetric ∧ p.IsHomogeneous 5 ∧
      ∀ a b t h : ℚ,
        generations * smFifthMoment a b t h =
          MvPolynomial.eval (ambientCartanCoordinates m n a b t h) p

/-- Representation-theoretic input in normalized finite-weight form: a full
ambient Weyl-invariant virtual character whose restricted fifth weight moment
is the physical target. -/
def HasAmbientWeylWeightCharacterSource
    (generations m n : ℚ) : Prop :=
  ∃ χ : AmbientWeylMoment.Character,
    AmbientWeylMoment.IsWeylInvariant χ ∧
      ∀ a b t h : ℚ,
        generations * smFifthMoment a b t h =
          AmbientWeylMoment.fifthMomentValue χ
            (ambientCartanCoordinates m n a b t h)

/-- The pure invariant-theory bridge: a symmetric homogeneous ambient fifth
moment supplies exactly the two-parameter extension used by the arithmetic
classification. -/
theorem hasFifthMomentExtension_of_weylInvariantSource
    (m n : ℚ) (H : HasWeylInvariantFifthMomentSource m n) :
    HasFifthMomentExtension m n := by
  rcases H with ⟨p, hSym, hHom, hp⟩
  rcases DegreeFiveWeylInvariant.symmetric_degreeFive_traceZero_span
      p hSym hHom with ⟨A, B, hAB⟩
  refine ⟨A, B, ?_⟩
  intro a b t h
  rw [hp a b t h]
  simpa [restrictedDegreeFiveInvariant,
    powerSumValue_ambientCartanCoordinates, mul_assoc] using
    hAB (ambientCartanCoordinates m n a b t h)
      (ambientCartanCoordinates_sum m n a b t h)

theorem scaledFifthMomentExtension_of_weylInvariantSource
    (generations m n : ℚ)
    (H : HasScaledWeylInvariantFifthMomentSource generations m n) :
    ∃ A B : ℚ, ∀ a b t h : ℚ,
      generations * smFifthMoment a b t h =
        restrictedDegreeFiveInvariant m n A B a b t h := by
  rcases H with ⟨p, hSym, hHom, hp⟩
  rcases DegreeFiveWeylInvariant.symmetric_degreeFive_traceZero_span
      p hSym hHom with ⟨A, B, hAB⟩
  refine ⟨A, B, ?_⟩
  intro a b t h
  rw [hp a b t h]
  simpa [restrictedDegreeFiveInvariant,
    powerSumValue_ambientCartanCoordinates, mul_assoc] using
    hAB (ambientCartanCoordinates m n a b t h)
      (ambientCartanCoordinates_sum m n a b t h)

theorem scaledWeylInvariantSource_of_ambientWeightCharacter
    (generations m n : ℚ)
    (H : HasAmbientWeylWeightCharacterSource generations m n) :
    HasScaledWeylInvariantFifthMomentSource generations m n := by
  rcases H with ⟨χ, hWeyl, hMoment⟩
  refine ⟨AmbientWeylMoment.fifthMomentPolynomial χ,
    AmbientWeylMoment.fifthMomentPolynomial_isSymmetric χ hWeyl,
    AmbientWeylMoment.fifthMomentPolynomial_isHomogeneous χ, ?_⟩
  intro a b t h
  rw [AmbientWeylMoment.eval_fifthMomentPolynomial]
  exact hMoment a b t h

/-- Exact coefficient recovery from seven rational evaluations.  In
particular, no nonstandard rational cocharacter has the required fifth
moment extension. -/
theorem eq_standard_of_hasFifthMomentExtension
    (m n : ℚ) (H : HasFifthMomentExtension m n) :
    m = -2 ∧ n = 3 := by
  rcases H with ⟨A, B, H⟩
  have e1 := H 1 1 0 0
  have e2 := H 2 (-1) 1 0
  norm_num [smFifthMoment, restrictedDegreeFiveInvariant, ambientPowerSum] at e1 e2
  have hB : B = 10 := by linarith
  have hA : A = -12 := by linarith
  subst A
  subst B
  have e0000 := H 0 0 0 1
  have e0010 := H 0 0 1 1
  have e1000 := H 1 0 0 1
  have e1010 := H 1 0 1 1
  have e1100 := H 1 1 0 1
  norm_num [smFifthMoment, restrictedDegreeFiveInvariant, ambientPowerSum] at e0000
  norm_num [smFifthMoment, restrictedDegreeFiveInvariant, ambientPowerSum] at e0010
  norm_num [smFifthMoment, restrictedDegreeFiveInvariant, ambientPowerSum] at e1000
  norm_num [smFifthMoment, restrictedDegreeFiveInvariant, ambientPowerSum] at e1010
  norm_num [smFifthMoment, restrictedDegreeFiveInvariant, ambientPowerSum] at e1100
  ring_nf at e0000 e0010 e1000 e1010 e1100
  have hLinear : m + n = 1 := by
    have h : -120 * (m + n - 1) = 0 := by
      linear_combination e1010 - e1000 - e0010 + e0000
    linarith
  have hQuadratic : 2 * m * n + n ^ 2 + 3 = 0 := by
    have h : 360 * (2 * m * n + n ^ 2 + 3) = 0 := by
      linear_combination e1100 - 3 * e1000 + 2 * e0000
    nlinarith
  have hCubic : 4 * m ^ 3 + 3 * m ^ 2 * n - 4 = 0 := by
    have h : 120 * (4 * m ^ 3 + 3 * m ^ 2 * n - 4) = 0 := by
      linear_combination e0010 - e0000
    nlinarith
  have hFactor : (n - 3) * (n + 1) = 0 := by
    nlinarith [hLinear, hQuadratic]
  rcases mul_eq_zero.mp hFactor with hn | hn
  · constructor <;> linarith
  · have hn' : n = -1 := by linarith
    have hm' : m = 2 := by linarith
    rw [hn', hm'] at hCubic
    norm_num at hCubic

theorem eq_standard_of_weylInvariantFifthMomentSource
    (m n : ℚ) (H : HasWeylInvariantFifthMomentSource m n) :
    m = -2 ∧ n = 3 :=
  eq_standard_of_hasFifthMomentExtension m n
    (hasFifthMomentExtension_of_weylInvariantSource m n H)

/-- The standard cocharacter really has the required degree-five extension,
with coefficients `A=-12` and `B=10`. -/
theorem standard_hasFifthMomentExtension :
    HasFifthMomentExtension (-2) 3 := by
  refine ⟨-12, 10, ?_⟩
  intro a b t h
  simp only [smFifthMoment, restrictedDegreeFiveInvariant, ambientPowerSum]
  ring

theorem hasFifthMomentExtension_iff (m n : ℚ) :
    HasFifthMomentExtension m n ↔ m = -2 ∧ n = 3 := by
  constructor
  · exact eq_standard_of_hasFifthMomentExtension m n
  · rintro ⟨rfl, rfl⟩
    exact standard_hasFifthMomentExtension

/-- Integer-pair form matching the physical centralizer lattice. -/
def IntegerPairHasFifthMomentExtension (mn : ℤ × ℤ) : Prop :=
  HasFifthMomentExtension (mn.1 : ℚ) (mn.2 : ℚ)

theorem eq_standardPair_of_integerPairHasFifthMomentExtension
    (mn : ℤ × ℤ) (H : IntegerPairHasFifthMomentExtension mn) :
    mn = standardPair := by
  have h := eq_standard_of_hasFifthMomentExtension
    (mn.1 : ℚ) (mn.2 : ℚ) H
  apply Prod.ext
  · change mn.1 = -2
    exact_mod_cast h.1
  · change mn.2 = 3
    exact_mod_cast h.2

/-- A nonzero number of identical generations gives the same unique
hypercharge pair: the generation factor can be absorbed into `A` and `B`. -/
theorem eq_standard_of_scaled_fifthMomentExtension
    (generations m n : ℚ) (hGenerations : generations ≠ 0)
    (H : ∃ A B : ℚ, ∀ a b t h : ℚ,
      generations * smFifthMoment a b t h =
        restrictedDegreeFiveInvariant m n A B a b t h) :
    m = -2 ∧ n = 3 := by
  rcases H with ⟨A, B, H⟩
  apply eq_standard_of_hasFifthMomentExtension m n
  refine ⟨A / generations, B / generations, ?_⟩
  intro a b t h
  have hAt := H a b t h
  rw [restrictedDegreeFiveInvariant] at hAt ⊢
  field_simp
  nlinarith

theorem eq_standard_of_scaled_weylInvariantFifthMomentSource
    (generations m n : ℚ) (hGenerations : generations ≠ 0)
    (H : HasScaledWeylInvariantFifthMomentSource generations m n) :
    m = -2 ∧ n = 3 :=
  eq_standard_of_scaled_fifthMomentExtension generations m n hGenerations
    (scaledFifthMomentExtension_of_weylInvariantSource generations m n H)

theorem eq_standard_of_ambientWeylWeightCharacterSource
    (generations m n : ℚ) (hGenerations : generations ≠ 0)
    (H : HasAmbientWeylWeightCharacterSource generations m n) :
    m = -2 ∧ n = 3 :=
  eq_standard_of_scaled_weylInvariantFifthMomentSource
    generations m n hGenerations
    (scaledWeylInvariantSource_of_ambientWeightCharacter generations m n H)

end FifthMomentHypercharge
end GUT
