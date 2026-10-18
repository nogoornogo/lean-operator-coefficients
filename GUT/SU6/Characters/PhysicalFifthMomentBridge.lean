import GUT.SU6.SelectionRules.StandardBranch.StandardPhysicalSource
import Mathlib.Tactic

/-!
# Exact physical weight characters and the fifth-moment bridge

The degree-five hypercharge argument uses a finite ambient `SU(6)` weight
character.  This file gives a non-analytic bridge from an exact physical
chiral spectrum to the fifth-moment identity required by that argument.

Ambient weights are pushed to rational linear forms in the four physical
Cartan variables `(a,b,t,h)`.  The target character is the explicit multiset
of the fifteen left-handed Standard Model weights.  An exact spectrum may
also contain arbitrary gauge singlets at zero weight; these make no
contribution to the fifth moment.
-/

open scoped BigOperators

namespace GUT
namespace PhysicalFifthMomentBridge

noncomputable section

abbrev PhysicalWeight := Fin 4 → ℚ
abbrev PhysicalCharacter := PhysicalWeight →₀ ℤ

/-- Evaluate a physical weight on the Cartan coordinates `(a,b,t,h)`. -/
def PhysicalWeight.eval (w : PhysicalWeight) (a b t h : ℚ) : ℚ :=
  w 0 * a + w 1 * b + w 2 * t + w 3 * h

/-- Restrict a trace-zero ambient weight along the centralizer cocharacter
with color and weak exponents `(m,n)`. -/
def restrictWeight (m n : ℚ) (w : AmbientWeylMoment.Weight) :
    PhysicalWeight :=
  ![w.coord 0 - w.coord 2,
    w.coord 1 - w.coord 2,
    w.coord 3 - w.coord 4,
    m * (w.coord 0 + w.coord 1 + w.coord 2) +
      n * (w.coord 3 + w.coord 4) + (-3 * m - 2 * n) * w.coord 5]

/-- Evaluation commutes with restriction of an ambient weight. -/
theorem restrictWeight_eval
    (m n a b t h : ℚ) (w : AmbientWeylMoment.Weight) :
    (restrictWeight m n w).eval a b t h =
      ∑ i, w.coord i *
        FifthMomentHypercharge.ambientCartanCoordinates m n a b t h i := by
  simp [restrictWeight, PhysicalWeight.eval,
    FifthMomentHypercharge.ambientCartanCoordinates, Fin.sum_univ_succ]
  ring

/-- Push an ambient normalized Laurent character to its physical rational
weight character.  `mapDomain` deliberately sums weight collisions. -/
def restrictCharacter (m n : ℚ)
    (p : AmbientWeightLattice.Character) : PhysicalCharacter :=
  Finsupp.mapDomain
    (restrictWeight m n ∘ AmbientWeightLattice.centeredWeight) p

/-- Fifth moment of a finite physical weight character. -/
def fifthMomentValue (p : PhysicalCharacter) (a b t h : ℚ) : ℚ :=
  p.sum fun w c => (c : ℚ) * (w.eval a b t h) ^ 5

theorem fifthMomentValue_zero (a b t h : ℚ) :
    fifthMomentValue 0 a b t h = 0 := by
  simp [fifthMomentValue]

theorem fifthMomentValue_single
    (w : PhysicalWeight) (c : ℤ) (a b t h : ℚ) :
    fifthMomentValue (Finsupp.single w c) a b t h =
      (c : ℚ) * (w.eval a b t h) ^ 5 := by
  simp [fifthMomentValue]

theorem fifthMomentValue_add
    (p q : PhysicalCharacter) (a b t h : ℚ) :
    fifthMomentValue (p + q) a b t h =
      fifthMomentValue p a b t h + fifthMomentValue q a b t h := by
  rw [fifthMomentValue, fifthMomentValue, fifthMomentValue,
    Finsupp.sum_add_index]
  · intro w _hw
    simp
  · intro w _hw c d
    rw [Int.cast_add]
    ring

/-- Scale all virtual multiplicities by an integer. -/
def zscale (k : ℤ) (p : PhysicalCharacter) : PhysicalCharacter :=
  Finsupp.mapRange (fun c : ℤ => k * c) (by simp) p

theorem fifthMomentValue_zscale
    (k : ℤ) (p : PhysicalCharacter) (a b t h : ℚ) :
    fifthMomentValue (zscale k p) a b t h =
      (k : ℚ) * fifthMomentValue p a b t h := by
  rw [fifthMomentValue, zscale, Finsupp.sum_mapRange_index]
  · calc
      p.sum (fun w c => ((k * c : ℤ) : ℚ) * (w.eval a b t h) ^ 5) =
          p.sum (fun w c =>
            (k : ℚ) * ((c : ℚ) * (w.eval a b t h) ^ 5)) := by
        apply Finsupp.sum_congr
        intro w _hw
        rw [Int.cast_mul]
        ring
      _ = (k : ℚ) *
          p.sum (fun w c => (c : ℚ) * (w.eval a b t h) ^ 5) := by
        simpa using (Finsupp.mul_sum (k : ℚ) p
          (f := fun w c => (c : ℚ) * (w.eval a b t h) ^ 5)).symm
  · intro w
    simp

/-- The fifteen left-handed Standard Model weights in the normalization used
by `FifthMomentHypercharge.smFifthMoment`. -/
def smWeight : Fin 15 → PhysicalWeight :=
  ![![1, 0, 1, 1],
    ![1, 0, -1, 1],
    ![0, 1, 1, 1],
    ![0, 1, -1, 1],
    ![-1, -1, 1, 1],
    ![-1, -1, -1, 1],
    ![-1, 0, 0, -4],
    ![0, -1, 0, -4],
    ![1, 1, 0, -4],
    ![-1, 0, 0, 2],
    ![0, -1, 0, 2],
    ![1, 1, 0, 2],
    ![0, 0, 1, -3],
    ![0, 0, -1, -3],
    ![0, 0, 0, 6]]

/-- The exact one-generation physical chiral weight character. -/
def smCharacter : PhysicalCharacter :=
  ∑ i : Fin 15, Finsupp.single (smWeight i) 1

theorem fifthMomentValue_smCharacter (a b t h : ℚ) :
    fifthMomentValue smCharacter a b t h =
      FifthMomentHypercharge.smFifthMoment a b t h := by
  simp [smCharacter, fifthMomentValue_add, fifthMomentValue_single,
    smWeight, PhysicalWeight.eval, FifthMomentHypercharge.smFifthMoment,
    Fin.sum_univ_succ]
  ring

/-- A zero physical weight records an arbitrary chiral gauge-singlet index. -/
def singletCharacter (singlets : ℤ) : PhysicalCharacter :=
  Finsupp.single 0 singlets

theorem fifthMomentValue_singletCharacter
    (singlets : ℤ) (a b t h : ℚ) :
    fifthMomentValue (singletCharacter singlets) a b t h = 0 := by
  simp [singletCharacter, fifthMomentValue_single, PhysicalWeight.eval]

/-- The fifth moment of a restricted ambient character is the ambient fifth
moment evaluated on the embedded physical Cartan. -/
theorem fifthMomentValue_restrictCharacter
    (p : AmbientWeightLattice.Character) (m n a b t h : ℚ) :
    fifthMomentValue (restrictCharacter m n p) a b t h =
      AmbientWeightLattice.fifthMomentValue p
        (FifthMomentHypercharge.ambientCartanCoordinates m n a b t h) := by
  rw [fifthMomentValue, restrictCharacter,
    Finsupp.sum_mapDomain_index]
  · apply Finsupp.sum_congr
    intro e _he
    rw [Function.comp_apply, restrictWeight_eval]
  · intro w
    simp
  · intro w c d
    rw [Int.cast_add]
    ring

/-- Exact SM-only chiral restriction, allowing an arbitrary net number of
physical gauge singlets. -/
def IsExactSMRestriction
    (p : AmbientWeightLattice.Character)
    (generations singlets : ℤ) (m n : ℚ) : Prop :=
  restrictCharacter m n p =
    zscale generations smCharacter + singletCharacter singlets

/-- The exact finite-weight physical spectrum supplies the previously
isolated `HasSMFifthMoment` premise. -/
theorem hasSMFifthMoment_of_exactSMRestriction
    (p : AmbientWeightLattice.Character)
    (generations singlets : ℤ) (m n : ℚ)
    (hExact : IsExactSMRestriction p generations singlets m n) :
    AmbientCharacterBridge.HasSMFifthMoment (generations : ℚ) m n p := by
  intro a b t h
  rw [← fifthMomentValue_restrictCharacter p m n a b t h,
    hExact, fifthMomentValue_add, fifthMomentValue_zscale,
    fifthMomentValue_smCharacter, fifthMomentValue_singletCharacter, add_zero]

/-- Consequently, any exact nonzero-generation physical restriction of an
actual finite virtual Laurent model forces the standard hypercharge pair. -/
theorem eq_standard_of_virtualModel_exactSMRestriction
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    (generations singlets : ℤ) (m n : ℚ)
    (hGenerations : generations ≠ 0)
    (hExact : IsExactSMRestriction M.poly generations singlets m n) :
    m = -2 ∧ n = 3 := by
  apply AmbientCharacterBridge.eq_standard_of_virtualModel_fifthMoment
    M (generations : ℚ) m n
  · exact_mod_cast hGenerations
  · exact hasSMFifthMoment_of_exactSMRestriction
      M.poly generations singlets m n hExact

/-- Fully sourced hypercharge character rigidity version: a finite virtual collection of actual
finite-dimensional jointly continuous unitary `SU(6)` representations,
together with its exact SM-only finite-weight restriction, forces the
standard hypercharge pair. -/
theorem eq_standard_of_continuousUnitarySource_exactSMRestriction
    {A : Type*}
    (source : StandardPhysicalSource.FiniteChargedContinuousUnitarySource A)
    (generations singlets : ℤ) (m n : ℚ)
    (hGenerations : generations ≠ 0)
    (hExact : IsExactSMRestriction source.ambientLaurentModel.poly
      generations singlets m n) :
    m = -2 ∧ n = 3 :=
  eq_standard_of_virtualModel_exactSMRestriction
    source.ambientLaurentModel generations singlets m n hGenerations hExact

end
end PhysicalFifthMomentBridge
end GUT
