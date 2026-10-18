import Math.RepresentationTheory.JointSourceData
import Math.RepresentationTheory.SU3SpinJointPresentation
import Math.RepresentationTheory.SU3DoubleSpinAllPresentation

/-! Executable colored core syntax. The retained summand order and tensor
parentheses match the actual presentations, including complementary degrees. -/
namespace Math.JointSourceData
set_option autoImplicit false
open JointSourceExpression

def dualKind : RestrictedColorWordSupport.Kind → RestrictedColorWordSupport.Kind
  | .symmetric n => .symmetricDual n
  | .oppositeSymmetric n => .oppositeSymmetricDual n
  | .symmetricDual n => .symmetric n
  | .oppositeSymmetricDual n => .oppositeSymmetric n
  | .square => .squareDual
  | .cube => .cubeDual
  | .squareSquare => .squareSquareDual
  | .adjoint => .adjointDual
  | .oppositeSquare => .oppositeSquareDual
  | .oppositeCube => .oppositeCubeDual
  | .oppositeSquareSquare => .oppositeSquareSquareDual
  | .oppositeAdjoint => .oppositeAdjointDual
  | .squareDual => .square
  | .cubeDual => .cube
  | .squareSquareDual => .squareSquare
  | .adjointDual => .adjoint
  | .oppositeSquareDual => .oppositeSquare
  | .oppositeCubeDual => .oppositeCube
  | .oppositeSquareSquareDual => .oppositeSquareSquare
  | .oppositeAdjointDual => .oppositeAdjoint


def dual : Expr → Expr
  | .zero => .zero
  | .atom a => .atom ⟨dualKind a.color,a.weak,a.leftSpin,a.rightSpin⟩
  | .sum l r => .sum (dual l) (dual r)
  | .tensor l r => .tensor (dual l) (dual r)

theorem dual_eq (e : Expr) : dual e = JointSourceDuality.dual e := by
  induction e with
  | zero => rfl
  | atom a => rfl
  | sum l r hl hr => exact congrArg₂ Expr.sum hl hr
  | tensor l r hl hr => exact congrArg₂ Expr.tensor hl hr

/-- A nonempty, right-associated sum; repeated summands remain distinct. -/
def sums (e : Expr) : List Expr → Expr
  | [] => e
  | x::xs => .sum e (sums x xs)

def colorWeak (k : RestrictedColorWordSupport.Kind) (n : Nat) : Expr :=
  .tensor (color k) (weak n)

def coloredOne (right : Bool) : Expr := .tensor (color (.symmetric 1)) (spin right 1)
def coloredTwo (right : Bool) : Expr :=
  .sum (.tensor (color (.oppositeSymmetric 1)) (spin right 2)) (color (.symmetric 2))
def coloredThree (right : Bool) : Expr :=
  .sum (spin right 3) (.tensor (color .adjoint) (spin right 1))

def colored (right : Bool) : Nat → Expr
  | 0 => scalar
  | 1 => coloredOne right
  | 2 => coloredTwo right
  | 3 => coloredThree right
  | 4 => dual (coloredTwo right)
  | 5 => dual (coloredOne right)
  | 6 => scalar
  | _+7 => .zero

theorem colored_eq (right : Bool) (n : Nat) :
    colored right n = (SU3SpinJointPresentation.positive right n).expression := by
  match n with
  | 0 => rfl
  | 1 => cases right <;> rfl
  | 2 => cases right <;> rfl
  | 3 => cases right <;> rfl
  | 4 => rw [colored, dual_eq]; cases right <;> rfl
  | 5 => rw [colored, dual_eq]; cases right <;> rfl
  | 6 => rfl
  | _+7 => rfl

theorem conjugateColored_eq (right : Bool) (n : Nat) :
    dual (colored right n) = (SU3SpinJointPresentation.negative right n).expression := by
  rw [dual_eq, colored_eq]
  rfl

def qOne (right : Bool) : Expr := .tensor (colorWeak (.symmetric 1) 1) (spin right 1)

def qTwo (right : Bool) : Expr :=
  .sum (.sum (.tensor (color (.oppositeSymmetric 1)) (pair right 2 2))
      (color (.oppositeSymmetric 1)))
    (.sum (.tensor (color (.symmetric 2)) (spin right 2)) (colorWeak (.symmetric 2) 2))

def qThree (right : Bool) : Expr :=
  .sum (.sum (pair right 3 3) (.tensor (colorWeak .adjoint 1) (spin right 3)))
    (.sum (.sum (pair right 1 1) (.tensor (colorWeak .adjoint 3) (spin right 1)))
      (.sum (.tensor (colorWeak (.symmetric 3) 1) (spin right 1))
        (.tensor (colorWeak .adjoint 1) (spin right 1))))

def qFourth : Expr := .sum (colorWeak (.symmetric 1) 2) (color (.oppositeSymmetric 2))
def qK211 : Expr :=
  .sum (colorWeak (.symmetric 1) 4)
    (.sum (.sum (colorWeak .square 2) (color .square))
      (.sum (colorWeak (.oppositeSymmetric 2) 2)
        (.sum (colorWeak (.symmetric 1) 2) (color (.symmetric 1)))))
def qK22 : Expr :=
  .sum (.sum (colorWeak (.oppositeSymmetric 2) 4) (color (.oppositeSymmetric 2)))
    (.sum (.sum (colorWeak (.symmetric 1) 2) (colorWeak .square 2)) (color (.symmetric 4)))
def qFour (right : Bool) : Expr :=
  .sum (.tensor qFourth (spin right 4)) (.sum (.tensor qK211 (spin right 2)) qK22)

def qFifthOne : Expr := sums (colorWeak (.oppositeSymmetric 1) 5)
  [colorWeak (.oppositeSymmetric 1) 3, colorWeak (.oppositeSymmetric 1) 1,
   colorWeak (.symmetric 2) 3, colorWeak (.symmetric 2) 1,
   colorWeak .oppositeSquare 3, colorWeak .oppositeSquare 1, colorWeak .cube 1]
def qFifthThree : Expr := sums (colorWeak (.symmetric 2) 3)
  [colorWeak (.oppositeSymmetric 1) 3, colorWeak (.symmetric 2) 1,
   colorWeak (.oppositeSymmetric 1) 1, colorWeak .oppositeSquare 1]
def qFive (right : Bool) : Expr :=
  .sum (.tensor (spin right 1) qFifthOne)
    (.sum (.tensor (spin right 3) qFifthThree)
      (.tensor (spin right 5) (colorWeak (.oppositeSymmetric 1) 1)))

def qSixthZero : Expr := sums (weak 6)
  [weak 2, colorWeak .adjoint 4, colorWeak .adjoint 2,
   color (.symmetric 3), color (.oppositeSymmetric 3), colorWeak .squareSquare 2]
def qSixthTwo : Expr := sums (weak 4)
  [colorWeak .adjoint 4, colorWeak .adjoint 2, colorWeak .adjoint 2,
   scalar, color .adjoint, colorWeak (.symmetric 3) 2,
   colorWeak (.oppositeSymmetric 3) 2, color .squareSquare]
def qSixthFour : Expr := sums (weak 2) [colorWeak .adjoint 2, color .adjoint]
def qSix (right : Bool) : Expr :=
  sums (.tensor (spin right 0) qSixthZero)
    [.tensor (spin right 2) qSixthTwo, .tensor (spin right 4) qSixthFour,
     .tensor (spin right 6) scalar]

def quark (right : Bool) : Nat → Expr
  | 0 => scalar
  | 1 => qOne right
  | 2 => qTwo right
  | 3 => qThree right
  | 4 => qFour right
  | 5 => qFive right
  | 6 => qSix right
  | 7 => dual (qFive right)
  | 8 => dual (qFour right)
  | 9 => dual (qThree right)
  | 10 => dual (qTwo right)
  | 11 => dual (qOne right)
  | 12 => dual scalar
  | _+13 => .zero

theorem qOne_eq (right : Bool) :
    qOne right = (SU3DoubleSpinLowerPresentation.positiveOne right).expression := by
  cases right <;> rfl

theorem qTwo_eq (right : Bool) :
    qTwo right = (SU3DoubleSpinLowerPresentation.positiveTwo right).expression := by
  cases right <;> rfl

theorem qThree_eq (right : Bool) :
    qThree right = (SU3DoubleSpinCubicPresentation.positiveThree right).expression := by
  cases right <;> rfl

theorem qFour_eq (right : Bool) :
    qFour right = (SU3DoubleSpinQuarticPresentation.positiveFour right).expression := by
  cases right <;> rfl

theorem qFive_eq (right : Bool) :
    qFive right = (SU3DoubleSpinFifthPresentation.positiveFive right).expression := by
  cases right <;> rfl

theorem qSix_eq (right : Bool) :
    qSix right = (SU3DoubleSpinSixthPresentation.positiveSix right).expression := by
  cases right <;> rfl

theorem qComplement7_eq (right : Bool) :
    dual (qFive right) = (SU3DoubleSpinFifthPresentation.positiveSeven right).expression := by
  rw [dual_eq, qFive_eq]
  rfl

theorem qComplement8_eq (right : Bool) :
    dual (qFour right) = (SU3DoubleSpinQuarticPresentation.positiveEight right).expression := by
  rw [dual_eq, qFour_eq]
  rfl

theorem qComplement9_eq (right : Bool) :
    dual (qThree right) = (SU3DoubleSpinCubicPresentation.positiveNine right).expression := by
  rw [dual_eq, qThree_eq]
  rfl

theorem qComplement10_eq (right : Bool) :
    dual (qTwo right) = (SU3DoubleSpinLowerPresentation.positiveTen right).expression := by
  rw [dual_eq, qTwo_eq]
  rfl

theorem qComplement11_eq (right : Bool) :
    dual (qOne right) = (SU3DoubleSpinLowerPresentation.positiveEleven right).expression := by
  rw [dual_eq, qOne_eq]
  rfl

theorem qTop_eq (right : Bool) :
    dual scalar = (SU3DoubleSpinLowerPresentation.positiveTwelve right).expression := by
  rw [dual_eq]
  rfl

theorem quark_eq (right : Bool) (n : Nat) :
    quark right n = (SU3DoubleSpinAllPresentation.positive right n).expression := by
  match n with
  | 0 => rfl
  | 1 => exact qOne_eq right
  | 2 => exact qTwo_eq right
  | 3 => exact qThree_eq right
  | 4 => exact qFour_eq right
  | 5 => exact qFive_eq right
  | 6 => exact qSix_eq right
  | 7 => exact qComplement7_eq right
  | 8 => exact qComplement8_eq right
  | 9 => exact qComplement9_eq right
  | 10 => exact qComplement10_eq right
  | 11 => exact qComplement11_eq right
  | 12 => exact qTop_eq right
  | _+13 => rfl

theorem conjugateQuark_eq (right : Bool) (n : Nat) :
    dual (quark right n) = (SU3DoubleSpinAllPresentation.negative right n).expression := by
  rw [dual_eq, quark_eq]
  rfl

end Math.JointSourceData
