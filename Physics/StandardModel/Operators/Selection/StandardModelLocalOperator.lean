import Physics.StandardModel.Operators.Selection.AbelianProtonCharacter
import Physics.StandardModel.Spectrum.Charges.ChargeResolved
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic

open Math

/-!
# Standard local Delta-B = 1 operators

This file gives the two proton-decay charge functionals a local-operator
meaning that does not assume a nonzero Wilson coefficient.  We use physical
right-handed fields, while `StandardBranchProtonObstruction.Charges` stores
the charges of the left-handed conjugate multiplets `u^c`, `d^c`, and `e^c`.
Consequently the right-handed fields carry the negatives of those stored
charges.

The two four-fermion signatures are the baryon-number-violating SMEFT
operators conventionally called `qque` and `duql`.  For each signature Lean
checks:

* three color fundamentals, contracted by the color epsilon tensor;
* two weak fundamentals, contracted by the weak epsilon tensor;
* two left- and two right-handed Weyl spinors, paired by Lorentz epsilon
  tensors;
* vanishing Standard Model hypercharge;
* canonical dimension six and Delta-B = Delta-L = 1; and
* equality of its residual Abelian character with the existing Abelian proton-operator neutrality proton
  character.

The determinant lemmas below verify that the epsilon tensors used by these
contraction certificates are nonzero and invariant under the corresponding
special-linear actions.  No coefficient or amplitude is attached to either
operator.
-/

open scoped BigOperators

namespace Physics
namespace StandardModelLocalOperator

open StandardBranchProtonObstruction
open FiniteAbelianChargeSectors
open StandardAbelianCharge

noncomputable section

universe u

/-- Physical chiral fermions used in the two standard dimension-six
baryon-number-violating operators. -/
inductive PhysicalFermion where
  | quarkDoublet
  | upRight
  | downRight
  | leptonDoublet
  | electronRight
  deriving DecidableEq

private def allPhysicalFermions : Finset PhysicalFermion :=
  {.quarkDoublet, .upRight, .downRight, .leptonDoublet, .electronRight}

/-- Number of slots occupied by one physical field species. -/
def fieldMultiplicity
    (O : Fin 4 → PhysicalFermion) (f : PhysicalFermion) : Nat :=
  (Finset.univ.filter fun i => O i = f).card

/-- Regroup a four-slot sum by physical field species. -/
theorem sum_eq_fieldMultiplicity_nsmul
    {A : Type*} [AddCommMonoid A]
    (O : Fin 4 → PhysicalFermion) (f : PhysicalFermion → A) :
    (∑ i, f (O i)) =
      fieldMultiplicity O .quarkDoublet • f .quarkDoublet +
      fieldMultiplicity O .upRight • f .upRight +
      fieldMultiplicity O .downRight • f .downRight +
      fieldMultiplicity O .leptonDoublet • f .leptonDoublet +
      fieldMultiplicity O .electronRight • f .electronRight := by
  have hMaps : ∀ i ∈ Finset.univ, O i ∈ allPhysicalFermions := by
    intro i hi
    cases O i <;> simp [allPhysicalFermions]
  rw [← Finset.sum_fiberwise_of_maps_to' hMaps f]
  simp [allPhysicalFermions, fieldMultiplicity, Finset.sum_const, add_assoc]

/-- A local four-fermion monomial is represented by its four ordered field
slots.  The order fixes the canonical epsilon pairings below. -/
abbrev FourFermionOperator := Fin 4 -> PhysicalFermion

/-- `q q u_R e_R` in physical-field conventions. -/
def qqueOperator : FourFermionOperator :=
  ![PhysicalFermion.quarkDoublet, PhysicalFermion.quarkDoublet,
    PhysicalFermion.upRight, PhysicalFermion.electronRight]

/-- `d_R u_R q l` in physical-field conventions. -/
def duqlOperator : FourFermionOperator :=
  ![PhysicalFermion.downRight, PhysicalFermion.upRight,
    PhysicalFermion.quarkDoublet, PhysicalFermion.leptonDoublet]

/-!
## Standard Model and Lorentz signatures

Hypercharge is stored as `6Y`, baryon number as `3B`, and canonical dimension
as twice the usual dimension.  This keeps all checks integral.
-/

def colorFundamentalMultiplicity : PhysicalFermion -> Nat
  | .quarkDoublet | .upRight | .downRight => 1
  | .leptonDoublet | .electronRight => 0

def weakFundamentalMultiplicity : PhysicalFermion -> Nat
  | .quarkDoublet | .leptonDoublet => 1
  | .upRight | .downRight | .electronRight => 0

def leftWeylMultiplicity : PhysicalFermion -> Nat
  | .quarkDoublet | .leptonDoublet => 1
  | .upRight | .downRight | .electronRight => 0

def rightWeylMultiplicity : PhysicalFermion -> Nat
  | .upRight | .downRight | .electronRight => 1
  | .quarkDoublet | .leptonDoublet => 0

/-- Six times physical hypercharge. -/
def sixHypercharge : PhysicalFermion -> Int
  | .quarkDoublet => 1
  | .upRight => 4
  | .downRight => -2
  | .leptonDoublet => -3
  | .electronRight => -6

/-- Three times physical baryon number. -/
def threeBaryonNumber : PhysicalFermion -> Int
  | .quarkDoublet | .upRight | .downRight => 1
  | .leptonDoublet | .electronRight => 0

def leptonNumber : PhysicalFermion -> Int
  | .leptonDoublet | .electronRight => 1
  | .quarkDoublet | .upRight | .downRight => 0

/-- Twice the canonical dimension of a Weyl fermion. -/
def twiceCanonicalDimension (_ : PhysicalFermion) : Nat := 3

structure QuantumNumbers where
  colorFundamentals : Nat
  weakFundamentals : Nat
  leftWeyl : Nat
  rightWeyl : Nat
  sixY : Int
  threeB : Int
  lepton : Int
  twiceDimension : Nat
  deriving DecidableEq

/-- The first three slots of a four-fermion monomial. -/
def firstThreeSlots : Fin 3 ↪ Fin 4 where
  toFun i := ⟨i, Nat.lt_trans i.isLt (by decide)⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin 4 => x.val) h

/-- The first two slots of a four-fermion monomial. -/
def firstTwoSlots : Fin 2 ↪ Fin 4 where
  toFun i := ⟨i, Nat.lt_trans i.isLt (by decide)⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin 4 => x.val) h

/-- The last two slots of a four-fermion monomial. -/
def lastTwoSlots : Fin 2 ↪ Fin 4 where
  toFun i := ⟨i.val + 2, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hij := congrArg (fun x : Fin 4 => x.val) h
    change i.val + 2 = j.val + 2 at hij
    omega

/-- Explicit assignment of field slots to the four non-Abelian determinant
contractions.  Injectivity prevents a field slot from being repeated within
one epsilon tensor. -/
structure EpsilonContractionPlan (O : FourFermionOperator) where
  colorSlots : Fin 3 ↪ Fin 4
  weakSlots : Fin 2 ↪ Fin 4
  leftSpinorSlots : Fin 2 ↪ Fin 4
  rightSpinorSlots : Fin 2 ↪ Fin 4
  colorFundamental :
    ∀ i, colorFundamentalMultiplicity (O (colorSlots i)) = 1
  weakFundamental :
    ∀ i, weakFundamentalMultiplicity (O (weakSlots i)) = 1
  leftWeyl : ∀ i, leftWeylMultiplicity (O (leftSpinorSlots i)) = 1
  rightWeyl : ∀ i, rightWeylMultiplicity (O (rightSpinorSlots i)) = 1

def qqueContractionPlan : EpsilonContractionPlan qqueOperator where
  colorSlots := firstThreeSlots
  weakSlots := firstTwoSlots
  leftSpinorSlots := firstTwoSlots
  rightSpinorSlots := lastTwoSlots
  colorFundamental := by intro i; fin_cases i <;> rfl
  weakFundamental := by intro i; fin_cases i <;> rfl
  leftWeyl := by intro i; fin_cases i <;> rfl
  rightWeyl := by intro i; fin_cases i <;> rfl

def duqlContractionPlan : EpsilonContractionPlan duqlOperator where
  colorSlots := firstThreeSlots
  weakSlots := lastTwoSlots
  leftSpinorSlots := lastTwoSlots
  rightSpinorSlots := firstTwoSlots
  colorFundamental := by intro i; fin_cases i <;> rfl
  weakFundamental := by intro i; fin_cases i <;> rfl
  leftWeyl := by intro i; fin_cases i <;> rfl
  rightWeyl := by intro i; fin_cases i <;> rfl

def quantumNumbers (O : FourFermionOperator) : QuantumNumbers where
  colorFundamentals := ∑ i, colorFundamentalMultiplicity (O i)
  weakFundamentals := ∑ i, weakFundamentalMultiplicity (O i)
  leftWeyl := ∑ i, leftWeylMultiplicity (O i)
  rightWeyl := ∑ i, rightWeylMultiplicity (O i)
  sixY := ∑ i, sixHypercharge (O i)
  threeB := ∑ i, threeBaryonNumber (O i)
  lepton := ∑ i, leptonNumber (O i)
  twiceDimension := ∑ i, twiceCanonicalDimension (O i)

theorem colorFundamentals_eq_fieldMultiplicities (O : FourFermionOperator) :
    (quantumNumbers O).colorFundamentals =
      fieldMultiplicity O .quarkDoublet +
        fieldMultiplicity O .upRight + fieldMultiplicity O .downRight := by
  change (∑ i, colorFundamentalMultiplicity (O i)) = _
  rw [sum_eq_fieldMultiplicity_nsmul]
  simp [colorFundamentalMultiplicity, add_assoc]

theorem weakFundamentals_eq_fieldMultiplicities (O : FourFermionOperator) :
    (quantumNumbers O).weakFundamentals =
      fieldMultiplicity O .quarkDoublet +
        fieldMultiplicity O .leptonDoublet := by
  change (∑ i, weakFundamentalMultiplicity (O i)) = _
  rw [sum_eq_fieldMultiplicity_nsmul]
  simp [weakFundamentalMultiplicity]

theorem rightWeyl_eq_fieldMultiplicities (O : FourFermionOperator) :
    (quantumNumbers O).rightWeyl =
      fieldMultiplicity O .upRight + fieldMultiplicity O .downRight +
        fieldMultiplicity O .electronRight := by
  change (∑ i, rightWeylMultiplicity (O i)) = _
  rw [sum_eq_fieldMultiplicity_nsmul]
  simp [rightWeylMultiplicity, add_assoc]

theorem lepton_eq_fieldMultiplicities (O : FourFermionOperator) :
    (quantumNumbers O).lepton =
      fieldMultiplicity O .leptonDoublet +
        fieldMultiplicity O .electronRight := by
  change (∑ i, leptonNumber (O i)) = _
  rw [sum_eq_fieldMultiplicity_nsmul]
  simp [leptonNumber]

theorem sixY_eq_fieldMultiplicities (O : FourFermionOperator) :
    (quantumNumbers O).sixY =
      (fieldMultiplicity O .quarkDoublet : Int) +
        4 * fieldMultiplicity O .upRight -
        2 * fieldMultiplicity O .downRight -
        3 * fieldMultiplicity O .leptonDoublet -
        6 * fieldMultiplicity O .electronRight := by
  change (∑ i, sixHypercharge (O i)) = _
  rw [sum_eq_fieldMultiplicity_nsmul]
  simp [sixHypercharge]
  ring

/-- The signature admits the standard color, weak, and two Lorentz epsilon
contractions and is neutral under hypercharge.  Tensor factors may be
permuted before applying the epsilon tensors. -/
def HasGaugeLorentzScalarContraction (O : FourFermionOperator) : Prop :=
  Nonempty (EpsilonContractionPlan O) /\
    (quantumNumbers O).colorFundamentals = 3 /\
    (quantumNumbers O).weakFundamentals = 2 /\
    (quantumNumbers O).leftWeyl = 2 /\
    (quantumNumbers O).rightWeyl = 2 /\
    (quantumNumbers O).sixY = 0

/-- Integral form of dimension six and `Delta B = Delta L = 1`. -/
def IsDimensionSixDeltaBOne (O : FourFermionOperator) : Prop :=
  (quantumNumbers O).twiceDimension = 12 /\
    (quantumNumbers O).threeB = 3 /\
    (quantumNumbers O).lepton = 1

def IsPhysicalDeltaBOneOperator (O : FourFermionOperator) : Prop :=
  HasGaugeLorentzScalarContraction O /\ IsDimensionSixDeltaBOne O

theorem qque_isPhysicalDeltaBOneOperator :
    IsPhysicalDeltaBOneOperator qqueOperator := by
  unfold IsPhysicalDeltaBOneOperator HasGaugeLorentzScalarContraction
    IsDimensionSixDeltaBOne
  constructor
  · refine ⟨⟨qqueContractionPlan⟩, ?_⟩
    decide
  · decide

theorem duql_isPhysicalDeltaBOneOperator :
    IsPhysicalDeltaBOneOperator duqlOperator := by
  unfold IsPhysicalDeltaBOneOperator HasGaugeLorentzScalarContraction
    IsDimensionSixDeltaBOne
  constructor
  · refine ⟨⟨duqlContractionPlan⟩, ?_⟩
    decide
  · decide

/-- Product of physical hypercharge phases in a four-fermion monomial. -/
def hyperchargePhase (O : FourFermionOperator) (z : Circle) : Circle :=
  ∏ i, z ^ sixHypercharge (O i)

theorem qque_hyperchargePhase (z : Circle) :
    hyperchargePhase qqueOperator z = 1 := by
  simp [hyperchargePhase, qqueOperator, sixHypercharge,
    Fin.prod_univ_four, zpow_neg]
  group

theorem duql_hyperchargePhase (z : Circle) :
    hyperchargePhase duqlOperator z = 1 := by
  simp [hyperchargePhase, duqlOperator, sixHypercharge,
    Fin.prod_univ_four, zpow_neg]
  group

/-!
## Nonzero invariant epsilon tensors
-/

/-- The epsilon contraction of `n` fundamental vectors, arranged as columns. -/
def epsilonContraction
    {n : Type*} [Fintype n] [DecidableEq n]
    (vectors : Matrix n n Complex) : Complex :=
  Matrix.det vectors

/-- The determinant epsilon tensor is invariant under every determinant-one
change of basis. -/
theorem epsilonContraction_invariant
    {n : Type*} [Fintype n] [DecidableEq n]
    (g : Matrix.SpecialLinearGroup n Complex)
    (vectors : Matrix n n Complex) :
    epsilonContraction ((g : Matrix n n Complex) * vectors) =
      epsilonContraction vectors := by
  simp [epsilonContraction, Matrix.det_mul]

/-- The epsilon contraction is not the zero multilinear form. -/
theorem epsilonContraction_one
    {n : Type*} [Fintype n] [DecidableEq n] :
    epsilonContraction (1 : Matrix n n Complex) = 1 := by
  simp [epsilonContraction]

theorem colorEpsilon_nonzero :
    epsilonContraction (1 : Matrix (Fin 3) (Fin 3) Complex) ≠ 0 := by
  simp [epsilonContraction]

theorem twoSpinorEpsilon_nonzero :
    epsilonContraction (1 : Matrix (Fin 2) (Fin 2) Complex) ≠ 0 := by
  simp [epsilonContraction]

/-!
## Residual ordinary-Abelian characters
-/

/-- Residual charge of a physical field.  Right-handed fields have the
opposite charge to the left-handed conjugates stored in `Charges`. -/
def physicalCharge
    {A : Type*} [AddCommGroup A] (k : Charges A) : PhysicalFermion -> A
  | .quarkDoublet => k.quark
  | .upRight => -k.up
  | .downRight => -k.down
  | .leptonDoublet => k.lepton
  | .electronRight => -k.electron

def operatorCharge
    {A : Type*} [AddCommGroup A]
    (k : Charges A) (O : FourFermionOperator) : A :=
  ∑ i, physicalCharge k (O i)

theorem operatorCharge_eq_fieldMultiplicities
    {A : Type*} [AddCommGroup A]
    (k : Charges A) (O : FourFermionOperator) :
    operatorCharge k O =
      fieldMultiplicity O .quarkDoublet • k.quark -
        fieldMultiplicity O .upRight • k.up -
        fieldMultiplicity O .downRight • k.down +
        fieldMultiplicity O .leptonDoublet • k.lepton -
        fieldMultiplicity O .electronRight • k.electron := by
  unfold operatorCharge
  rw [sum_eq_fieldMultiplicity_nsmul]
  simp [physicalCharge]
  abel

theorem qque_operatorCharge
    {A : Type*} [AddCommGroup A] (k : Charges A) :
    operatorCharge k qqueOperator = protonFirst k := by
  simp [operatorCharge, qqueOperator, physicalCharge, protonFirst,
    Fin.sum_univ_four]
  abel

theorem duql_operatorCharge
    {A : Type*} [AddCommGroup A] (k : Charges A) :
    operatorCharge k duqlOperator = protonSecond k := by
  simp [operatorCharge, duqlOperator, physicalCharge, protonSecond,
    Fin.sum_univ_four]
  abel

/-- Every four-fermion signature satisfying the declared dimension-six
`Delta B = Delta L = 1` gauge/Lorentz conditions has, independently of slot
order, one of the two standard proton-operator charges. -/
theorem operatorCharge_eq_protonFirst_or_protonSecond_of_isPhysical
    {A : Type*} [AddCommGroup A]
    (k : Charges A) (O : FourFermionOperator)
    (hO : IsPhysicalDeltaBOneOperator O) :
    operatorCharge k O = protonFirst k ∨
      operatorCharge k O = protonSecond k := by
  rcases hO with
    ⟨⟨_, hColor, hWeak, _, hRight, hY⟩, _, _, hLepton⟩
  let q := fieldMultiplicity O .quarkDoublet
  let u := fieldMultiplicity O .upRight
  let d := fieldMultiplicity O .downRight
  let l := fieldMultiplicity O .leptonDoublet
  let e := fieldMultiplicity O .electronRight
  have hColor' : q + u + d = 3 := by
    calc
      q + u + d = (quantumNumbers O).colorFundamentals := by
        simpa [q, u, d] using
          (colorFundamentals_eq_fieldMultiplicities O).symm
      _ = 3 := hColor
  have hWeak' : q + l = 2 := by
    calc
      q + l = (quantumNumbers O).weakFundamentals := by
        simpa [q, l] using
          (weakFundamentals_eq_fieldMultiplicities O).symm
      _ = 2 := hWeak
  have hRight' : u + d + e = 2 := by
    calc
      u + d + e = (quantumNumbers O).rightWeyl := by
        simpa [u, d, e] using
          (rightWeyl_eq_fieldMultiplicities O).symm
      _ = 2 := hRight
  have hLepton' : (l : Int) + e = 1 := by
    calc
      l + e = (quantumNumbers O).lepton := by
        simpa [l, e] using (lepton_eq_fieldMultiplicities O).symm
      _ = 1 := hLepton
  have hY' :
      (q : Int) + 4 * u - 2 * d - 3 * l - 6 * e = 0 := by
    calc
      (q : Int) + 4 * u - 2 * d - 3 * l - 6 * e =
          (quantumNumbers O).sixY := by
        simpa [q, u, d, l, e] using
          (sixY_eq_fieldMultiplicities O).symm
      _ = 0 := hY
  have hCounts :
      (q = 2 ∧ u = 1 ∧ d = 0 ∧ l = 0 ∧ e = 1) ∨
        (q = 1 ∧ u = 1 ∧ d = 1 ∧ l = 1 ∧ e = 0) := by
    omega
  rw [operatorCharge_eq_fieldMultiplicities]
  change
    (q • k.quark - u • k.up - d • k.down + l • k.lepton -
        e • k.electron = protonFirst k) ∨
      (q • k.quark - u • k.up - d • k.down + l • k.lepton -
        e • k.electron = protonSecond k)
  rcases hCounts with
    ⟨hq, hu, hd, hl, he⟩ | ⟨hq, hu, hd, hl, he⟩
  · left
    rw [hq, hu, hd, hl, he]
    simp [protonFirst]
    abel
  · right
    rw [hq, hu, hd, hl, he]
    simp [protonSecond]
    abel

/-- The residual character multiplying a local four-fermion monomial. -/
def operatorCharacter
    {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H)) (O : FourFermionOperator) : H →* Circle :=
  (operatorCharge k O).toMul

theorem qque_operatorCharacter
    {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H)) :
    operatorCharacter k qqueOperator = protonFirstCharacter k := by
  simpa [operatorCharacter, protonFirstCharacter] using
    congrArg Additive.toMul (qque_operatorCharge k)

theorem duql_operatorCharacter
    {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H)) :
    operatorCharacter k duqlOperator = protonSecondCharacter k := by
  simpa [operatorCharacter, protonSecondCharacter] using
    congrArg Additive.toMul (duql_operatorCharge k)

/-- Character-level form of the exhaustive physical-signature
classification. -/
theorem operatorCharacter_eq_protonFirst_or_protonSecond_of_isPhysical
    {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H)) (O : FourFermionOperator)
    (hO : IsPhysicalDeltaBOneOperator O) :
    operatorCharacter k O = protonFirstCharacter k ∨
      operatorCharacter k O = protonSecondCharacter k := by
  rcases operatorCharge_eq_protonFirst_or_protonSecond_of_isPhysical k O hO with
    hFirst | hSecond
  · left
    simpa [operatorCharacter, protonFirstCharacter] using
      congrArg Additive.toMul hFirst
  · right
    simpa [operatorCharacter, protonSecondCharacter] using
      congrArg Additive.toMul hSecond

inductive StandardOperatorClass where
  | qque
  | duql
  deriving DecidableEq

def StandardOperatorClass.operator :
    StandardOperatorClass → FourFermionOperator
  | .qque => qqueOperator
  | .duql => duqlOperator

theorem StandardOperatorClass.isPhysicalDeltaBOneOperator
    (O : StandardOperatorClass) :
    IsPhysicalDeltaBOneOperator O.operator := by
  cases O
  · exact qque_isPhysicalDeltaBOneOperator
  · exact duql_isPhysicalDeltaBOneOperator

def StandardOperatorClass.residualCharacter
    {H : Type u} [CommGroup H]
    (O : StandardOperatorClass) (k : Charges (ChargeLabel H)) : H →* Circle :=
  operatorCharacter k O.operator

@[simp]
theorem qque_residualCharacter
    {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H)) :
    StandardOperatorClass.qque.residualCharacter k =
      protonFirstCharacter k :=
  qque_operatorCharacter k

@[simp]
theorem duql_residualCharacter
    {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H)) :
    StandardOperatorClass.duql.residualCharacter k =
      protonSecondCharacter k :=
  duql_operatorCharacter k

/-- An ordinary Abelian charge rule forbids all two canonical local operator
classes exactly when neither class has the trivial residual character. -/
def ForbidsAllStandardOperators
    {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H)) : Prop :=
  ∀ O : StandardOperatorClass, O.residualCharacter k ≠ 1

theorem forbidsAllStandardOperators_iff
    {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H)) :
    ForbidsAllStandardOperators k ↔
      protonFirstCharacter k ≠ 1 ∧ protonSecondCharacter k ≠ 1 := by
  constructor
  · intro h
    constructor
    · rw [← qque_residualCharacter k]
      exact h .qque
    · rw [← duql_residualCharacter k]
      exact h .duql
  · rintro ⟨hFirst, hSecond⟩ O
    cases O
    · simpa using hFirst
    · simpa using hSecond

/-- Selection-rule protection at the charge-resolved spectrum level.  It
quantifies over actual supported field sectors but makes no statement about
Wilson coefficients. -/
def ForbidsEverySupportedStandardOperator
    {H : Type u} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H)) : Prop :=
  ∀ k : Charges (ChargeLabel H),
    ChargesSupported p k → ForbidsAllStandardOperators k

/-- The literal universal selection-rule target: every supported local
four-fermion operator satisfying the declared physical `Delta B = 1`
predicate has nontrivial residual character.  The two canonical classes form
a subset of this larger quantification. -/
def ForbidsEverySupportedPhysicalDeltaBOneOperator
    {H : Type u} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H)) : Prop :=
  ∀ k : Charges (ChargeLabel H),
    ChargesSupported p k →
      ∀ O : FourFermionOperator,
        IsPhysicalDeltaBOneOperator O → operatorCharacter k O ≠ 1

/-- A charge rule forbidding every physically admissible operator in
particular forbids both canonical standard classes. -/
theorem forbidsEverySupportedPhysicalDeltaBOneOperator_implies_standard
    {H : Type u} [CommGroup H]
    {p : ResolvedCharacter (ChargeLabel H)}
    (h : ForbidsEverySupportedPhysicalDeltaBOneOperator p) :
    ForbidsEverySupportedStandardOperator p := by
  intro k hk O
  exact h k hk O.operator O.isPhysicalDeltaBOneOperator

/-- For the declared four-fermion physical predicate, forbidding the two
standard classes already forbids every admissible signature. -/
theorem forbidsEverySupportedStandardOperator_implies_physicalDeltaBOne
    {H : Type u} [CommGroup H]
    {p : ResolvedCharacter (ChargeLabel H)}
    (h : ForbidsEverySupportedStandardOperator p) :
    ForbidsEverySupportedPhysicalDeltaBOneOperator p := by
  intro k hk O hO
  have hStandard := (forbidsAllStandardOperators_iff k).mp (h k hk)
  rcases operatorCharacter_eq_protonFirst_or_protonSecond_of_isPhysical k O hO with
    hFirst | hSecond
  · rw [hFirst]
    exact hStandard.1
  · rw [hSecond]
    exact hStandard.2

theorem forbidsEverySupportedPhysicalDeltaBOneOperator_iff_standard
    {H : Type u} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H)) :
    ForbidsEverySupportedPhysicalDeltaBOneOperator p ↔
      ForbidsEverySupportedStandardOperator p :=
  ⟨forbidsEverySupportedPhysicalDeltaBOneOperator_implies_standard,
    forbidsEverySupportedStandardOperator_implies_physicalDeltaBOne⟩

/-- Positive witness that an actual set of supported field sectors forms a
canonical local operator left invariant by the residual Abelian symmetry. -/
structure SupportedInvariantOperator
    {H : Type u} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H)) where
  charges : Charges (ChargeLabel H)
  supported : ChargesSupported p charges
  operator : StandardOperatorClass
  invariant : operator.residualCharacter charges = 1

theorem SupportedInvariantOperator.isPhysicalDeltaBOneOperator
    {H : Type u} [CommGroup H]
    {p : ResolvedCharacter (ChargeLabel H)}
    (w : SupportedInvariantOperator p) :
    IsPhysicalDeltaBOneOperator w.operator.operator :=
  w.operator.isPhysicalDeltaBOneOperator

def supportedQque
    {H : Type u} [CommGroup H]
    {p : ResolvedCharacter (ChargeLabel H)}
    (k : Charges (ChargeLabel H)) (hk : ChargesSupported p k)
    (hInvariant : protonFirstCharacter k = 1) :
    SupportedInvariantOperator p where
  charges := k
  supported := hk
  operator := .qque
  invariant := by simpa using hInvariant

def supportedDuql
    {H : Type u} [CommGroup H]
    {p : ResolvedCharacter (ChargeLabel H)}
    (k : Charges (ChargeLabel H)) (hk : ChargesSupported p k)
    (hInvariant : protonSecondCharacter k = 1) :
    SupportedInvariantOperator p where
  charges := k
  supported := hk
  operator := .duql
  invariant := by simpa using hInvariant

theorem SupportedInvariantOperator.not_forbidsEverySupportedStandardOperator
    {H : Type u} [CommGroup H]
    {p : ResolvedCharacter (ChargeLabel H)}
    (w : SupportedInvariantOperator p) :
    ¬ ForbidsEverySupportedStandardOperator p := by
  intro hForbids
  exact (hForbids w.charges w.supported w.operator) w.invariant

/-- A single supported canonical operator with trivial character directly
refutes a charge rule purporting to forbid every physically admissible local
`Delta B = 1` operator. -/
theorem SupportedInvariantOperator.not_forbidsEverySupportedPhysicalDeltaBOneOperator
    {H : Type u} [CommGroup H]
    {p : ResolvedCharacter (ChargeLabel H)}
    (w : SupportedInvariantOperator p) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator p := by
  intro hForbids
  exact
    (hForbids w.charges w.supported w.operator.operator
      w.isPhysicalDeltaBOneOperator) w.invariant

theorem forbidsEverySupportedStandardOperator_iff
    {H : Type u} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H)) :
    ForbidsEverySupportedStandardOperator p ↔
      ∀ k : Charges (ChargeLabel H),
        ChargesSupported p k →
          protonFirstCharacter k ≠ 1 ∧ protonSecondCharacter k ≠ 1 := by
  constructor
  · intro h k hk
    exact (forbidsAllStandardOperators_iff k).mp (h k hk)
  · intro h k hk
    exact (forbidsAllStandardOperators_iff k).mpr (h k hk)

end
end StandardModelLocalOperator
end Physics
