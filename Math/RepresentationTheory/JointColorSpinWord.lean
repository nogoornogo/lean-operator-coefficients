import Math.RepresentationTheory.RestrictedColorWordSupport
import Math.RepresentationTheory.SU2TensorWordSupport
import Math.RepresentationTheory.ExternalCoefficientSupport

/-! Simultaneous positive support for arbitrary tensor words of actual
color factors and three independent SU2 labels. A single word choice retains
color, weak, left spin and right spin jointly before group factorization. -/
namespace Math.JointColorSpinWord
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct

abbrev Group := SU3DefiningExterior.Group × (TauCeti.SU2 × (TauCeti.SU2 × TauCeti.SU2))

structure Atom where
  color : RestrictedColorWordSupport.Kind
  weak : ℕ
  leftSpin : ℕ
  rightSpin : ℕ

inductive Word
  | leaf (atom : Atom)
  | tensor (left right : Word)

def colorWord : Word → RestrictedColorWordSupport.Word
  | .leaf a => .leaf a.color
  | .tensor l r => .tensor (colorWord l) (colorWord r)
def weakWord : Word → SU2TensorWordSupport.Word
  | .leaf a => .leaf a.weak
  | .tensor l r => .tensor (weakWord l) (weakWord r)
def leftWord : Word → SU2TensorWordSupport.Word
  | .leaf a => .leaf a.leftSpin
  | .tensor l r => .tensor (leftWord l) (leftWord r)
def rightWord : Word → SU2TensorWordSupport.Word
  | .leaf a => .leaf a.rightSpin
  | .tensor l r => .tensor (rightWord l) (rightWord r)

abbrev color (w : Word) := RestrictedColorWordSupport.action (colorWord w)
abbrev weak (w : Word) := SU2TensorWordSupport.action (weakWord w)
abbrev leftSpin (w : Word) := SU2TensorWordSupport.action (leftWord w)
abbrev rightSpin (w : Word) := SU2TensorWordSupport.action (rightWord w)
abbrev spins (w : Word) := external (leftSpin w) (rightSpin w)
abbrev lower (w : Word) := external (weak w) (spins w)
abbrev normalized (w : Word) := external (color w) (lower w)

structure Data where
  Carrier : Type
  [additive : AddCommGroup Carrier]
  [linear : Module ℂ Carrier]
  [finite : Module.Finite ℂ Carrier]
  action : Representation ℂ Group Carrier
attribute [instance] Data.additive Data.linear Data.finite

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance (n : ℕ) : AddCommGroup (Sym[ℂ]^n WeakDoubletScalars.Doublet) :=
  Module.addCommMonoidToAddCommGroup ℂ

def atomData (a : Atom) : Data := by
  let := ColorFlagVertex.finite (RestrictedColorWordSupport.model a.color)
  let T := (RestrictedColorWordSupport.model a.color).Carrier ⊗[ℂ]
    ((Sym[ℂ]^a.weak WeakDoubletScalars.Doublet) ⊗[ℂ]
      ((Sym[ℂ]^a.leftSpin WeakDoubletScalars.Doublet) ⊗[ℂ]
        (Sym[ℂ]^a.rightSpin WeakDoubletScalars.Doublet)))
  have hf : Module.Finite ℂ T := inferInstance
  exact { Carrier := T, finite := hf, action := normalized (.leaf a) }

def data : Word → Data
  | .leaf a => atomData a
  | .tensor l r =>
    { Carrier := (data l).Carrier ⊗[ℂ] (data r).Carrier
      action := (data l).action.tprod (data r).action }

abbrev Carrier (w : Word) := (data w).Carrier
abbrev action (w : Word) := (data w).action

def flatten : (w : Word) → Representation.Equiv (action w) (normalized w)
  | .leaf _ => .refl _
  | .tensor l r =>
    (tensorEquiv (flatten l) (flatten r)).trans
      ((regroupPair (color l) (color r) (lower l) (lower r)).trans
        (externalEquiv (.refl _) ((regroupPair (weak l) (weak r) (spins l) (spins r)).trans
          (externalEquiv (.refl _)
            (regroupPair (leftSpin l) (leftSpin r) (rightSpin l) (rightSpin r))))))

def Supports (w : Word) : Prop :=
  RestrictedColorWordSupport.Supports (colorWord w) ∧
    SU2TensorWordSupport.Supports (weakWord w) ∧
      SU2TensorWordSupport.Supports (leftWord w) ∧ SU2TensorWordSupport.Supports (rightWord w)

theorem allowed_iff (w : Word) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (action w)) ↔ Supports w := by
  rw [SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv (flatten w))]
  simp only [normalized,lower,spins,ExternalCoefficientSupport.allowed_iff,
    color,weak,leftSpin,rightSpin,RestrictedColorWordSupport.allowed_iff,
    SU2TensorWordSupport.allowed_iff,Supports]

theorem forbidden_iff (w : Word) :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants (action w)) ↔ ¬ Supports w := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,allowed_iff]

def withHiggs (w : Word) (m : ℕ) : Word := .tensor w (.leaf ⟨.symmetric 0,m,0,0⟩)

end
end Math.JointColorSpinWord
