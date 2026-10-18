import GUT.SU6.Characters.PhysicalFifthMomentBridge
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

/-!
# Physical compact-torus character bridge

This file connects the exact rational finite-weight hypothesis used by the
fifth-moment argument to equality of actual character functions on the compact
physical Cartan torus.  For an integral centralizer pair `(m,n)`, restriction
first lands in the integral four-dimensional physical weight lattice.  A
faithful multivariable Fourier evaluator then recovers that finite weight
character from its values on `Circle^4`.
-/

open scoped BigOperators

namespace GUT
namespace PhysicalTorusCharacterBridge

noncomputable section

open PhysicalFifthMomentBridge

abbrev PhysicalExponent := Fin 4 → ℤ
abbrev IntegralPhysicalCharacter := PhysicalExponent →₀ ℤ

/-- Cast an integral physical torus character to its rational weight. -/
def exponentWeight (e : PhysicalExponent) : PhysicalWeight :=
  fun i => (e i : ℚ)

theorem exponentWeight_injective : Function.Injective exponentWeight := by
  intro e f h
  funext i
  have hi := congrFun h i
  change (e i : ℚ) = (f i : ℚ) at hi
  exact_mod_cast hi

/-- Pass from the integral compact-torus character to the rational weight
model used by the fifth-moment calculation. -/
def toRationalCharacter (p : IntegralPhysicalCharacter) : PhysicalCharacter :=
  Finsupp.mapDomain exponentWeight p

theorem toRationalCharacter_injective :
    Function.Injective toRationalCharacter :=
  Finsupp.mapDomain_injective exponentWeight_injective

/-- Restriction of a canonical ambient exponent along an integral physical
centralizer cocharacter. -/
def restrictExponent (m n : ℤ) (e : AmbientWeightLattice.Exponent) :
    PhysicalExponent :=
  ![e 0 - e 2,
    e 1 - e 2,
    e 3 - e 4,
    m * (e 0 + e 1 + e 2) + n * (e 3 + e 4)]

/-- The integral and centered-rational descriptions of weight restriction
agree exactly. -/
theorem exponentWeight_restrictExponent
    (m n : ℤ) (e : AmbientWeightLattice.Exponent) :
    exponentWeight (restrictExponent m n e) =
      restrictWeight (m : ℚ) (n : ℚ)
        (AmbientWeightLattice.centeredWeight e) := by
  have h0 : AmbientWeightLattice.rawCoord e (0 : Fin 6) = e 0 := by
    simpa using AmbientWeightLattice.rawCoord_castSucc e (0 : Fin 5)
  have h1 : AmbientWeightLattice.rawCoord e (1 : Fin 6) = e 1 := by
    simpa using AmbientWeightLattice.rawCoord_castSucc e (1 : Fin 5)
  have h2 : AmbientWeightLattice.rawCoord e (2 : Fin 6) = e 2 := by
    simpa using AmbientWeightLattice.rawCoord_castSucc e (2 : Fin 5)
  have h3 : AmbientWeightLattice.rawCoord e (3 : Fin 6) = e 3 := by
    simpa using AmbientWeightLattice.rawCoord_castSucc e (3 : Fin 5)
  have h4 : AmbientWeightLattice.rawCoord e (4 : Fin 6) = e 4 := by
    simpa using AmbientWeightLattice.rawCoord_castSucc e (4 : Fin 5)
  have h5 : AmbientWeightLattice.rawCoord e (5 : Fin 6) = 0 := by
    simpa using AmbientWeightLattice.rawCoord_last e
  ext i
  fin_cases i <;>
    simp [exponentWeight, restrictExponent, restrictWeight,
      AmbientWeightLattice.centeredWeight, AmbientWeightLattice.center,
      Fin.sum_univ_succ, h0, h1, h2, h3, h4, h5] ;
    ring

/-- Push every ambient monomial to its integral physical weight, summing all
collisions. -/
def restrictIntegralCharacter (m n : ℤ)
    (p : AmbientWeightLattice.Character) : IntegralPhysicalCharacter :=
  Finsupp.mapDomain (restrictExponent m n) p

theorem toRationalCharacter_restrictIntegralCharacter
    (m n : ℤ) (p : AmbientWeightLattice.Character) :
    toRationalCharacter (restrictIntegralCharacter m n p) =
      restrictCharacter (m : ℚ) (n : ℚ) p := by
  unfold toRationalCharacter restrictIntegralCharacter restrictCharacter
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro e _he
  exact exponentWeight_restrictExponent m n e

/-!
## Faithful Fourier evaluation
-/

/-- Evaluation of an integral physical finite-weight character on the compact
four-torus. -/
def eval (p : IntegralPhysicalCharacter) (x : UnitAddTorus (Fin 4)) : ℂ :=
  p.sum fun e c => (c : ℂ) * UnitAddTorus.mFourier e x

namespace Fourier

def exponentMonoidHom
    (e : PhysicalExponent) : Multiplicative (UnitAddTorus (Fin 4)) →* ℂ where
  toFun x := UnitAddTorus.mFourier e (Multiplicative.toAdd x)
  map_one' := by
    simp [UnitAddTorus.mFourier]
  map_mul' := by
    intro x y
    simp [UnitAddTorus.mFourier, AddCircle.toCircle_add,
      Finset.prod_mul_distrib]

theorem mFourier_injective :
    Function.Injective (UnitAddTorus.mFourier (d := Fin 4)) := by
  intro e f h
  have hLp :
      UnitAddTorus.mFourierLp (d := Fin 4) 2 e =
        UnitAddTorus.mFourierLp (d := Fin 4) 2 f := by
    dsimp [UnitAddTorus.mFourierLp]
    rw [h]
  exact (UnitAddTorus.orthonormal_mFourier
    (d := Fin 4)).linearIndependent.injective hLp

theorem exponentMonoidHom_injective :
    Function.Injective exponentMonoidHom := by
  intro e f h
  apply mFourier_injective
  ext x
  have hx := congrArg
    (fun phi : Multiplicative (UnitAddTorus (Fin 4)) →* ℂ =>
      phi (Multiplicative.ofAdd x)) h
  change UnitAddTorus.mFourier e x = UnitAddTorus.mFourier f x at hx
  exact hx

theorem linearIndependent_exponentMonoidHom :
    LinearIndependent ℂ
      (fun e : PhysicalExponent =>
        (exponentMonoidHom e :
          Multiplicative (UnitAddTorus (Fin 4)) → ℂ)) := by
  exact (linearIndependent_monoidHom
      (Multiplicative (UnitAddTorus (Fin 4))) ℂ).comp
    exponentMonoidHom exponentMonoidHom_injective

def toComplex (p : IntegralPhysicalCharacter) : PhysicalExponent →₀ ℂ :=
  Finsupp.mapRange (fun c : ℤ => (c : ℂ)) (by simp) p

@[simp]
theorem toComplex_apply (p : IntegralPhysicalCharacter) (e : PhysicalExponent) :
    toComplex p e = (p e : ℂ) := by
  simp [toComplex]

theorem eval_eq_linearCombination (p : IntegralPhysicalCharacter) :
    Finsupp.linearCombination ℂ
        (fun e : PhysicalExponent =>
          (exponentMonoidHom e :
            Multiplicative (UnitAddTorus (Fin 4)) → ℂ))
        (toComplex p) =
      fun x => eval p (Multiplicative.toAdd x) := by
  ext x
  rw [Finsupp.linearCombination_apply, toComplex,
    Finsupp.sum_mapRange_index]
  · simp only [eval, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    apply Finset.sum_congr rfl
    intro e _he
    rfl
  · intro e
    simp

theorem eval_faithful :
    ∀ p q : IntegralPhysicalCharacter,
      (∀ x : UnitAddTorus (Fin 4), eval p x = eval q x) → p = q := by
  intro p q h
  have hlin :
      Finsupp.linearCombination ℂ
          (fun e : PhysicalExponent =>
            (exponentMonoidHom e :
              Multiplicative (UnitAddTorus (Fin 4)) → ℂ))
          (toComplex p) =
        Finsupp.linearCombination ℂ
          (fun e : PhysicalExponent =>
            (exponentMonoidHom e :
              Multiplicative (UnitAddTorus (Fin 4)) → ℂ))
          (toComplex q) := by
    rw [eval_eq_linearCombination p, eval_eq_linearCombination q]
    funext x
    exact h (Multiplicative.toAdd x)
  have hC : toComplex p = toComplex q :=
    linearIndependent_exponentMonoidHom.finsuppLinearCombination_injective hlin
  ext e
  exact Int.cast_injective (α := ℂ) (by
    simpa [toComplex_apply] using
      congrArg (fun r : PhysicalExponent →₀ ℂ => r e) hC)

end Fourier

/-!
## The integral Standard Model target
-/

/-- The same fifteen physical weights as `smWeight`, now in the integral
compact-torus character lattice. -/
def smExponent : Fin 15 → PhysicalExponent :=
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

theorem exponentWeight_smExponent (i : Fin 15) :
    exponentWeight (smExponent i) = smWeight i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [exponentWeight, smExponent, smWeight]

def integralSMCharacter : IntegralPhysicalCharacter :=
  ∑ i : Fin 15, Finsupp.single (smExponent i) 1

def integralSingletCharacter (singlets : ℤ) : IntegralPhysicalCharacter :=
  Finsupp.single 0 singlets

def zscale (k : ℤ) (p : IntegralPhysicalCharacter) :
    IntegralPhysicalCharacter :=
  Finsupp.mapRange (fun c : ℤ => k * c) (by simp) p

theorem toRationalCharacter_integralSMCharacter :
    toRationalCharacter integralSMCharacter = smCharacter := by
  unfold toRationalCharacter integralSMCharacter smCharacter
  change
    (Finsupp.mapDomain.addMonoidHom exponentWeight)
        (∑ i : Fin 15, Finsupp.single (smExponent i) 1) =
      ∑ i : Fin 15, Finsupp.single (smWeight i) 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  change
    Finsupp.mapDomain exponentWeight (Finsupp.single (smExponent i) 1) =
      Finsupp.single (smWeight i) 1
  rw [Finsupp.mapDomain_single]
  exact congrArg (fun w => Finsupp.single w 1)
    (exponentWeight_smExponent i)

theorem toRationalCharacter_integralSingletCharacter (singlets : ℤ) :
    toRationalCharacter (integralSingletCharacter singlets) =
      singletCharacter singlets := by
  have hzero : exponentWeight 0 = 0 := by
    ext i
    simp [exponentWeight]
  simp [toRationalCharacter, integralSingletCharacter, singletCharacter,
    hzero]

theorem toRationalCharacter_zscale
    (k : ℤ) (p : IntegralPhysicalCharacter) :
    toRationalCharacter (zscale k p) =
      PhysicalFifthMomentBridge.zscale k (toRationalCharacter p) := by
  unfold toRationalCharacter zscale PhysicalFifthMomentBridge.zscale
  exact Finsupp.mapDomain_mapRange exponentWeight p
    (fun c : ℤ => k * c) (by simp) (by
      intro c d
      ring)

def exactSMCharacter (generations singlets : ℤ) :
    IntegralPhysicalCharacter :=
  zscale generations integralSMCharacter +
    integralSingletCharacter singlets

theorem toRationalCharacter_exactSMCharacter
    (generations singlets : ℤ) :
    toRationalCharacter (exactSMCharacter generations singlets) =
      PhysicalFifthMomentBridge.zscale generations smCharacter +
        singletCharacter singlets := by
  calc
    toRationalCharacter (exactSMCharacter generations singlets) =
        toRationalCharacter (zscale generations integralSMCharacter) +
          toRationalCharacter (integralSingletCharacter singlets) := by
      exact Finsupp.mapDomain_add
    _ = PhysicalFifthMomentBridge.zscale generations smCharacter +
          singletCharacter singlets := by
      rw [toRationalCharacter_zscale,
        toRationalCharacter_integralSMCharacter,
        toRationalCharacter_integralSingletCharacter]

/-!
## The physical compact torus inside the ambient torus
-/

/-- The four physical compact-torus coordinates `(a,b,t,h)` embedded in the
five independent ambient diagonal coordinates. -/
def ambientTorusPoint (m n : ℤ) (x : UnitAddTorus (Fin 4)) :
    UnitAddTorus (Fin 5) :=
  ![x 0 + m • x 3,
    x 1 + m • x 3,
    -x 0 - x 1 + m • x 3,
    x 2 + n • x 3,
    -x 2 + n • x 3]

def fourierPairing {d : Type*} [Fintype d]
    (e : d → ℤ) (x : UnitAddTorus d) : AddCircle (1 : ℝ) :=
  ∑ i, e i • x i

theorem mFourier_eq_toCircle_fourierPairing
    {d : Type*} [Fintype d] (e : d → ℤ) (x : UnitAddTorus d) :
    UnitAddTorus.mFourier e x =
      (AddCircle.toCircle (fourierPairing e x) : ℂ) := by
  have hcircle :
      AddCircle.toCircle (∑ i, e i • x i) =
        ∏ i, AddCircle.toCircle (e i • x i) := by
    classical
    induction (Finset.univ : Finset d) using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha,
          AddCircle.toCircle_add, ih]
  change
    (∏ i, (AddCircle.toCircle (e i • x i) : ℂ)) =
      (AddCircle.toCircle (∑ i, e i • x i) : ℂ)
  have hcoe :
      (∏ i, (AddCircle.toCircle (e i • x i) : ℂ)) =
        ((∏ i, AddCircle.toCircle (e i • x i) : Circle) : ℂ) := by
    classical
    induction (Finset.univ : Finset d) using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, ih]
        rfl
  rw [hcoe]
  exact congrArg Subtype.val hcircle.symm

/-- Pulling an ambient Fourier monomial back along `ambientTorusPoint` gives
the monomial indexed by `restrictExponent`. -/
theorem mFourier_ambientTorusPoint
    (m n : ℤ) (e : AmbientWeightLattice.Exponent)
    (x : UnitAddTorus (Fin 4)) :
    UnitAddTorus.mFourier e (ambientTorusPoint m n x) =
      UnitAddTorus.mFourier (restrictExponent m n e) x := by
  rw [mFourier_eq_toCircle_fourierPairing,
    mFourier_eq_toCircle_fourierPairing]
  have hpairing :
      fourierPairing e (ambientTorusPoint m n x) =
        fourierPairing (restrictExponent m n e) x := by
    simp [fourierPairing, ambientTorusPoint, restrictExponent,
      Fin.sum_univ_succ, add_smul, sub_smul, smul_add, smul_sub,
      smul_neg, smul_smul]
    module
  exact congrArg Subtype.val (congrArg AddCircle.toCircle hpairing)

theorem eval_restrictIntegralCharacter
    (m n : ℤ) (p : AmbientWeightLattice.Character)
    (x : UnitAddTorus (Fin 4)) :
    eval (restrictIntegralCharacter m n p) x =
      AmbientLaurent.Fourier.evalUnitAddTorus p
        (ambientTorusPoint m n x) := by
  rw [eval, restrictIntegralCharacter, Finsupp.sum_mapDomain_index,
    AmbientLaurent.Fourier.evalUnitAddTorus]
  · apply Finsupp.sum_congr
    intro e _he
    rw [mFourier_ambientTorusPoint]
  · intro e
    simp
  · intro e c d
    rw [Int.cast_add]
    ring

/-!
## From actual character equality to the exact finite-weight hypothesis
-/

/-- The actual determinant-one diagonal matrix reached by a point of the
physical compact four-torus. -/
def physicalDiagonalPoint (m n : ℤ) (x : UnitAddTorus (Fin 4)) :
    AmbientLaurent.DiagonalPoint :=
  AmbientLaurent.DiagonalPoint.ofUnitAddTorus (ambientTorusPoint m n x)

theorem eval_restrictIntegralCharacter_eq_diagonalEval
    (m n : ℤ) (p : AmbientWeightLattice.Character)
    (x : UnitAddTorus (Fin 4)) :
    eval (restrictIntegralCharacter m n p) x =
      AmbientLaurent.diagonalEval p (physicalDiagonalPoint m n x) := by
  calc
    eval (restrictIntegralCharacter m n p) x =
        AmbientLaurent.Fourier.evalUnitAddTorus p
          (ambientTorusPoint m n x) :=
      eval_restrictIntegralCharacter m n p x
    _ = AmbientLaurent.eval p
          (AmbientLaurent.torusVecOfUnitAddTorus
            (ambientTorusPoint m n x)) :=
      (AmbientLaurent.eval_torusVecOfUnitAddTorus p
        (ambientTorusPoint m n x)).symm
    _ = AmbientLaurent.diagonalEval p
          (physicalDiagonalPoint m n x) := by
      simp [AmbientLaurent.diagonalEval, physicalDiagonalPoint,
        AmbientLaurent.DiagonalPoint.toTorusVec_ofUnitAddTorus]

/-- Function-level formulation of an exact SM-only chiral character on the
actual compact physical torus. -/
def IsExactSMCharacterOnPhysicalTorus
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (generations singlets : ℤ) (m n : ℤ) : Prop :=
  ∀ x : UnitAddTorus (Fin 4),
    AmbientCharacterBridge.finiteVirtualRestrictedCharacter chi
        (physicalDiagonalPoint m n x) =
      eval (exactSMCharacter generations singlets) x

/-- Faithfulness of the physical Fourier evaluator turns function-level
character equality into the exact finite-weight equality used by hypercharge character rigidity. -/
theorem exactSMRestriction_of_characterOnPhysicalTorus
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    (generations singlets : ℤ) (m n : ℤ)
    (hExact : IsExactSMCharacterOnPhysicalTorus
      (chi := chi) generations singlets m n) :
    IsExactSMRestriction M.poly generations singlets (m : ℚ) (n : ℚ) := by
  have hIntegral :
      restrictIntegralCharacter m n M.poly =
        exactSMCharacter generations singlets := by
    apply Fourier.eval_faithful
    intro x
    rw [eval_restrictIntegralCharacter_eq_diagonalEval,
      M.evaluates_character]
    exact hExact x
  calc
    restrictCharacter (m : ℚ) (n : ℚ) M.poly =
        toRationalCharacter (restrictIntegralCharacter m n M.poly) :=
      (toRationalCharacter_restrictIntegralCharacter m n M.poly).symm
    _ = toRationalCharacter (exactSMCharacter generations singlets) := by
      rw [hIntegral]
    _ = PhysicalFifthMomentBridge.zscale generations smCharacter +
          singletCharacter singlets :=
      toRationalCharacter_exactSMCharacter generations singlets

/-- An actual finite virtual Laurent character with exact SM-only character
on the compact physical torus has the standard integral cocharacter pair. -/
theorem eq_standard_of_virtualModel_characterOnPhysicalTorus
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    (generations singlets : ℤ) (m n : ℤ)
    (hGenerations : generations ≠ 0)
    (hExact : IsExactSMCharacterOnPhysicalTorus
      (chi := chi) generations singlets m n) :
    m = -2 ∧ n = 3 := by
  have hStandard : (m : ℚ) = -2 ∧ (n : ℚ) = 3 :=
    PhysicalFifthMomentBridge.eq_standard_of_virtualModel_exactSMRestriction
      M generations singlets (m : ℚ) (n : ℚ) hGenerations
        (exactSMRestriction_of_characterOnPhysicalTorus
          M generations singlets m n hExact)
  constructor
  · exact_mod_cast hStandard.1
  · exact_mod_cast hStandard.2

/-- Fully sourced continuous-unitary specialization of the function-level hypercharge character rigidity
bridge. -/
theorem eq_standard_of_continuousUnitarySource_characterOnPhysicalTorus
    {A : Type*}
    (source : StandardPhysicalSource.FiniteChargedContinuousUnitarySource A)
    (generations singlets : ℤ) (m n : ℤ)
    (hGenerations : generations ≠ 0)
    (hExact : IsExactSMCharacterOnPhysicalTorus
      (chi := source.toVirtual) generations singlets m n) :
    m = -2 ∧ n = 3 :=
  eq_standard_of_virtualModel_characterOnPhysicalTorus
    source.ambientLaurentModel generations singlets m n hGenerations hExact

end
end PhysicalTorusCharacterBridge
end GUT
