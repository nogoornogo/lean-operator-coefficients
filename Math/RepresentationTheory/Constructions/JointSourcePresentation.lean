import Math.RepresentationTheory.Constructions.JointSourceAtoms

/-! Actual source presentations compose without exposing underlying Cauchy
or quotient maps. Every presentation stores a proved representation
equivalence, while its support condition is only the finite joint syntax. -/
namespace Math.JointSourcePresentation
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection JointColorSpinWord

variable {A B C : Type*} [AddCommMonoid A] [Module ℂ A]
  [AddCommMonoid B] [Module ℂ B] [AddCommMonoid C] [Module ℂ C]

structure Presentation (rho : Representation ℂ Group A) where
  expression : JointSourceExpression.Expr
  equivalence : Representation.Equiv rho (JointSourceExpression.action expression)

def zero (a : Representation ℂ Group A) (h : ∀ x : A, x=0) : Presentation a :=
  ⟨.zero,JointSourceExpression.zeroEquivalence a h⟩

def alongEquiv {a : Representation ℂ Group A} {b : Representation ℂ Group B}
    (e : Representation.Equiv a b) (P : Presentation b) : Presentation a :=
  ⟨P.expression,e.trans P.equivalence⟩

def sum {a : Representation ℂ Group A} {b : Representation ℂ Group B}
    (P : Presentation a) (Q : Presentation b) : Presentation (a.prod b) :=
  ⟨.sum P.expression Q.expression,prodEquiv P.equivalence Q.equivalence⟩

def tensor {a : Representation ℂ Group A} {b : Representation ℂ Group B}
    (P : Presentation a) (Q : Presentation b) : Presentation (a.tprod b) :=
  ⟨.tensor P.expression Q.expression,tensorEquiv P.equivalence Q.equivalence⟩

def dual {a : Representation ℂ Group A} (P : Presentation a) : Presentation a.dual :=
  ⟨JointSourceDuality.dual P.expression,
    (dualEquiv P.equivalence).trans (JointSourceDuality.equivalence P.expression)⟩

def color (k : RestrictedColorWordSupport.Kind) : Presentation (JointSourceAtoms.color k) :=
  ⟨.atom ⟨k,0,0,0⟩,JointSourceAtoms.colorOnly k⟩
def weak (n : ℕ) : Presentation (JointSourceAtoms.weak n) :=
  ⟨.atom ⟨.symmetric 0,n,0,0⟩,JointSourceAtoms.weakOnly n⟩
def leftSpin (n : ℕ) : Presentation (JointSourceAtoms.leftSpin n) :=
  ⟨.atom ⟨.symmetric 0,0,n,0⟩,JointSourceAtoms.leftOnly n⟩
def rightSpin (n : ℕ) : Presentation (JointSourceAtoms.rightSpin n) :=
  ⟨.atom ⟨.symmetric 0,0,0,n⟩,JointSourceAtoms.rightOnly n⟩
def scalar : Presentation (trivial ℂ Group ℂ) :=
  ⟨.atom ⟨.symmetric 0,0,0,0⟩,JointSourceAtoms.scalar⟩

def tensorComp {K : Type*} [Group K]
    (a : Representation ℂ K A) (b : Representation ℂ K B) (j : Group →* K)
    (P : Presentation (a.comp j)) (Q : Presentation (b.comp j)) : Presentation ((a.tprod b).comp j) :=
  alongEquiv { toLinearEquiv := .refl ℂ _, isIntertwining' _ := rfl } (tensor P Q)

def sumComp {K : Type*} [Group K]
    (a : Representation ℂ K A) (b : Representation ℂ K B) (j : Group →* K)
    (P : Presentation (a.comp j)) (Q : Presentation (b.comp j)) : Presentation ((a.prod b).comp j) :=
  alongEquiv { toLinearEquiv := .refl ℂ _, isIntertwining' _ := rfl } (sum P Q)

def externalComp {K L : Type*} [Group K] [Group L]
    (a : Representation ℂ K A) (b : Representation ℂ L B) (j : Group →* K × L)
    (P : Presentation (a.comp ((MonoidHom.fst _ _).comp j)))
    (Q : Presentation (b.comp ((MonoidHom.snd _ _).comp j))) :
    Presentation ((external a b).comp j) :=
  alongEquiv { toLinearEquiv := .refl ℂ _, isIntertwining' _ := rfl } (tensor P Q)

def dualComp {K : Type*} [Group K] (a : Representation ℂ K A) (j : Group →* K)
    (P : Presentation (a.comp j)) : Presentation (a.dual.comp j) :=
  alongEquiv
    { toLinearEquiv := .refl ℂ _
      isIntertwining' g := by
        apply LinearMap.ext
        intro f
        apply LinearMap.ext
        intro x
        change f (a ((j g)⁻¹) x) = f (a (j g⁻¹) x)
        rw [map_inv j] }
    (dual P)

theorem allowed_iff {a : Representation ℂ Group A} (P : Presentation a) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants a) ↔
      JointSourceExpression.Supports P.expression :=
  (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv P.equivalence)).trans
    (JointSourceExpression.allowed_iff P.expression)

theorem forbidden_iff {a : Representation ℂ Group A} (P : Presentation a) :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants a) ↔
      ¬ JointSourceExpression.Supports P.expression := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,allowed_iff P]

end
end Math.JointSourcePresentation
