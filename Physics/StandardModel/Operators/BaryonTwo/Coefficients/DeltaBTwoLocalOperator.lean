import Physics.StandardModel.Operators.Selection.StandardModelLocalOperator

open Math

/-!
# Local six-quark Delta-B = 2 grading

This module records quantum numbers and ordinary-Abelian residual characters
for one physical, all-right-handed `uudd dd` monomial. It is a local-operator
grading statement. It does not construct a six-field coefficient, prove basis
completeness, or attach matching, QCD matrix elements, rates or amplitudes.
-/

open scoped BigOperators

namespace Physics.DeltaBTwoLocalOperator

set_option autoImplicit false
noncomputable section

open StandardBranchProtonObstruction
open FiniteAbelianChargeSectors
open StandardModelLocalOperator

universe u

/-- An ordered six-fermion monomial in the existing physical-field convention. -/
abbrev SixFermionOperator := Fin 6 → PhysicalFermion

/-- The one-generation all-right-handed `uudd dd` field pattern. The ordering
groups the fields as two `udd` color triples. -/
def udduddOperator : SixFermionOperator :=
  ![PhysicalFermion.upRight, PhysicalFermion.downRight,
    PhysicalFermion.downRight, PhysicalFermion.upRight,
    PhysicalFermion.downRight, PhysicalFermion.downRight]

/-- Six-slot quantum numbers, using the integral normalizations `6Y`, `3B`
and twice the canonical dimension from `StandardModelLocalOperator`. -/
def quantumNumbers (O : SixFermionOperator) : QuantumNumbers where
  colorFundamentals := ∑ i, colorFundamentalMultiplicity (O i)
  weakFundamentals := ∑ i, weakFundamentalMultiplicity (O i)
  leftWeyl := ∑ i, leftWeylMultiplicity (O i)
  rightWeyl := ∑ i, rightWeylMultiplicity (O i)
  sixY := ∑ i, sixHypercharge (O i)
  threeB := ∑ i, threeBaryonNumber (O i)
  lepton := ∑ i, leptonNumber (O i)
  twiceDimension := ∑ i, twiceCanonicalDimension (O i)

/-- Integral quantum-number formulation of a dimension-nine, `Delta B = 2`,
`Delta L = 0` six-fermion monomial. -/
def IsDimensionNineDeltaBTwo (O : SixFermionOperator) : Prop :=
  (quantumNumbers O).twiceDimension = 18 ∧
    (quantumNumbers O).threeB = 6 ∧
    (quantumNumbers O).lepton = 0

/-- The declared pattern has six color fundamentals, no weak indices, six
right-handed Weyl fields and zero hypercharge. Explicit contractions are a
separate construction. -/
def IsAllRightHandedGaugeNeutralSixQuark (O : SixFermionOperator) : Prop :=
  (quantumNumbers O).colorFundamentals = 6 ∧
    (quantumNumbers O).weakFundamentals = 0 ∧
    (quantumNumbers O).leftWeyl = 0 ∧
    (quantumNumbers O).rightWeyl = 6 ∧
    (quantumNumbers O).sixY = 0

theorem uddudd_quantumNumbers :
    quantumNumbers udduddOperator =
      { colorFundamentals := 6
        weakFundamentals := 0
        leftWeyl := 0
        rightWeyl := 6
        sixY := 0
        threeB := 6
        lepton := 0
        twiceDimension := 18 } := by
  decide

theorem uddudd_isDimensionNineDeltaBTwo :
    IsDimensionNineDeltaBTwo udduddOperator := by
  rw [IsDimensionNineDeltaBTwo, uddudd_quantumNumbers]
  decide

theorem uddudd_isAllRightHandedGaugeNeutralSixQuark :
    IsAllRightHandedGaugeNeutralSixQuark udduddOperator := by
  rw [IsAllRightHandedGaugeNeutralSixQuark, uddudd_quantumNumbers]
  decide

/-- Three times baryon number is an additive grading on ordered monomials. -/
def baryonGrade (O : SixFermionOperator) : ℤ :=
  ∑ i, threeBaryonNumber (O i)

@[simp] theorem baryonGrade_eq (O : SixFermionOperator) :
    baryonGrade O = (quantumNumbers O).threeB := rfl

@[simp] theorem uddudd_baryonGrade : baryonGrade udduddOperator = 6 := by
  simpa using congrArg QuantumNumbers.threeB uddudd_quantumNumbers

/-- Residual ordinary-Abelian charge of a six-field physical monomial. -/
def operatorCharge {A : Type*} [AddCommGroup A]
    (k : Charges A) (O : SixFermionOperator) : A :=
  ∑ i, physicalCharge k (O i)

/-- Residual charge of the all-right-handed `(udd)^2` pattern. Physical
right-handed fields carry the negatives of the stored left-handed-conjugate
charges. -/
def udduddCharge {A : Type*} [AddCommGroup A] (k : Charges A) : A :=
  -(2 • k.up + 4 • k.down)

theorem uddudd_operatorCharge {A : Type*} [AddCommGroup A] (k : Charges A) :
    operatorCharge k udduddOperator = udduddCharge k := by
  simp [operatorCharge, udduddOperator, physicalCharge, udduddCharge,
    Fin.sum_univ_succ]
  abel

/-- Residual character multiplying the ordered six-quark monomial. -/
def operatorCharacter {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H)) (O : SixFermionOperator) : H →* Circle :=
  (operatorCharge k O).toMul

/-- A residual character prohibits the monomial at the grading level when it
is nontrivial. This does not assert that a neutral coefficient is generated. -/
def ResidualProhibits {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H)) (O : SixFermionOperator) : Prop :=
  operatorCharacter k O ≠ 1

theorem residualProhibits_iff_charge_ne_zero {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H)) (O : SixFermionOperator) :
    ResidualProhibits k O ↔ operatorCharge k O ≠ 0 := by
  change (operatorCharge k O).toMul ≠ 1 ↔ operatorCharge k O ≠ 0
  constructor
  · intro h hc
    apply h
    rw [hc]
    rfl
  · intro h hc
    apply h
    apply Additive.toMul.injective
    simpa using hc

theorem uddudd_residualProhibits_iff {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H)) :
    ResidualProhibits k udduddOperator ↔ udduddCharge k ≠ 0 := by
  rw [residualProhibits_iff_charge_ne_zero, uddudd_operatorCharge]

end
end Physics.DeltaBTwoLocalOperator
