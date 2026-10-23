import Math.RepresentationTheory.Constructions.JointSourceExpression
import Math.RepresentationTheory.Color.Diagrams.RestrictedColorKindDuality
import Math.RepresentationTheory.Decomposition.ExternalTensorDual
import Math.RepresentationTheory.SU2.SU2FiniteCoupling

/-! Actual contragredients stay inside the joint-source syntax. Color duals
use the proved concrete kind dictionary; each independent SU2 factor uses
its own perfect self-duality. -/
namespace Math.JointSourceDuality
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open JointSourceExpression JointColorSpinWord
open scoped TensorProduct

def atomDual (a : Atom) : Atom :=
  ⟨RestrictedColorKindDuality.dual a.color,a.weak,a.leftSpin,a.rightSpin⟩

def atomEquivalence (a : Atom) : Representation.Equiv
    (JointColorSpinWord.action (.leaf a)).dual (JointColorSpinWord.action (.leaf (atomDual a))) := by
  letI : Module.Finite ℂ (RestrictedColorWordSupport.Carrier (colorWord (.leaf a))) :=
    ColorFlagVertex.finite (RestrictedColorWordSupport.model a.color)
  letI : Module.Finite ℂ (SU2TensorWordSupport.Carrier (weakWord (.leaf a))) :=
    inferInstanceAs (Module.Finite ℂ (Sym[ℂ]^a.weak WeakDoubletScalars.Doublet))
  letI : Module.Finite ℂ (SU2TensorWordSupport.Carrier (leftWord (.leaf a))) :=
    inferInstanceAs (Module.Finite ℂ (Sym[ℂ]^a.leftSpin WeakDoubletScalars.Doublet))
  letI : Module.Finite ℂ (SU2TensorWordSupport.Carrier (rightWord (.leaf a))) :=
    inferInstanceAs (Module.Finite ℂ (Sym[ℂ]^a.rightSpin WeakDoubletScalars.Doublet))
  exact (ExternalTensorDual.equiv (color (.leaf a)) (lower (.leaf a))).symm.trans
    (externalEquiv (RestrictedColorKindDuality.equivalence a.color)
      ((ExternalTensorDual.equiv (weak (.leaf a)) (spins (.leaf a))).symm.trans
        (externalEquiv (SU2FiniteCoupling.selfDual a.weak).symm
          ((ExternalTensorDual.equiv (leftSpin (.leaf a)) (rightSpin (.leaf a))).symm.trans
            (externalEquiv (SU2FiniteCoupling.selfDual a.leftSpin).symm
              (SU2FiniteCoupling.selfDual a.rightSpin).symm)))))

def dual : Expr → Expr
  | .zero => .zero
  | .atom a => .atom (atomDual a)
  | .sum l r => .sum (dual l) (dual r)
  | .tensor l r => .tensor (dual l) (dual r)

def equivalence : (e : Expr) → Representation.Equiv
    (JointSourceExpression.action e).dual (JointSourceExpression.action (dual e))
  | .zero => JointSourceExpression.zeroEquivalence _ (fun _x => Subsingleton.elim _ _)
  | .atom a => atomEquivalence a
  | .sum l r =>
    (dualProdEquiv (JointSourceExpression.action l) (JointSourceExpression.action r)).symm.trans
      (prodEquiv (equivalence l) (equivalence r))
  | .tensor l r =>
    (InvariantTensorCurry.tensorDual (JointSourceExpression.action l) (JointSourceExpression.action r)).symm.trans
      (tensorEquiv (equivalence l) (equivalence r))

end
end Math.JointSourceDuality
