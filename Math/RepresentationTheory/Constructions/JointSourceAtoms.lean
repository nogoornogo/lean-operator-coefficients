import Math.RepresentationTheory.Constructions.JointSourceDuality

/-! Actual joint-atom normalization: retain a color factor and the three
independent symmetric-spin labels, inserting only proved scalar units. -/
namespace Math.JointSourceAtoms
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open JointColorSpinWord
open scoped TensorProduct

def colorProjection : Group →* SU3DefiningExterior.Group := MonoidHom.fst _ _
def weakProjection : Group →* TauCeti.SU2 := (MonoidHom.fst _ _).comp (MonoidHom.snd _ _)
def leftProjection : Group →* TauCeti.SU2 :=
  (MonoidHom.fst _ _).comp ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _))
def rightProjection : Group →* TauCeti.SU2 :=
  (MonoidHom.snd _ _).comp ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _))

abbrev color (k : RestrictedColorWordSupport.Kind) :
    Representation ℂ Group (RestrictedColorWordSupport.model k).Carrier := (RestrictedColorWordSupport.model k).action.comp colorProjection
abbrev weak (n : ℕ) : Representation ℂ Group (Sym[ℂ]^n WeakDoubletScalars.Doublet) := (WeakDoubletScalars.doublet.symmetricPower n).comp weakProjection
abbrev leftSpin (n : ℕ) : Representation ℂ Group (Sym[ℂ]^n WeakDoubletScalars.Doublet) := (WeakDoubletScalars.doublet.symmetricPower n).comp leftProjection
abbrev rightSpin (n : ℕ) : Representation ℂ Group (Sym[ℂ]^n WeakDoubletScalars.Doublet) := (WeakDoubletScalars.doublet.symmetricPower n).comp rightProjection

def colorZero : Representation.Equiv (color (.symmetric 0)) (trivial ℂ Group ℂ) :=
  restrictEquiv (SymmetricPowerLowDegree.representationZeroEquiv SU3DefiningExterior.rho) colorProjection
def weakZero : Representation.Equiv (weak 0) (trivial ℂ Group ℂ) :=
  restrictEquiv (SymmetricPowerLowDegree.representationZeroEquiv WeakDoubletScalars.doublet) weakProjection
def leftZero : Representation.Equiv (leftSpin 0) (trivial ℂ Group ℂ) :=
  restrictEquiv (SymmetricPowerLowDegree.representationZeroEquiv WeakDoubletScalars.doublet) leftProjection
def rightZero : Representation.Equiv (rightSpin 0) (trivial ℂ Group ℂ) :=
  restrictEquiv (SymmetricPowerLowDegree.representationZeroEquiv WeakDoubletScalars.doublet) rightProjection

def atom (k : RestrictedColorWordSupport.Kind) (w l r : ℕ) : Representation.Equiv
    ((color k).tprod ((weak w).tprod ((leftSpin l).tprod (rightSpin r))))
      (JointSourceExpression.action (.atom ⟨k,w,l,r⟩)) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' _ := rfl

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

def rightUnit (a : Representation ℂ Group A) {b : Representation ℂ Group B}
    (e : Representation.Equiv b (trivial ℂ Group ℂ)) : Representation.Equiv a (a.tprod b) :=
  (Representation.TensorProduct.rid ℂ a).symm.trans (tensorEquiv (.refl a) e.symm)

def leftUnit (a : Representation ℂ Group A) {b : Representation ℂ Group B}
    (e : Representation.Equiv b (trivial ℂ Group ℂ)) : Representation.Equiv a (b.tprod a) :=
  (Representation.TensorProduct.lid ℂ a).symm.trans (tensorEquiv e.symm (.refl a))

@[reducible] local instance (n : ℕ) : AddCommGroup (Sym[ℂ]^n WeakDoubletScalars.Doublet) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance (X Y : Type*) [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] : AddCommGroup (X ⊗[ℂ] Y) := inferInstance

def leftPad (k : RestrictedColorWordSupport.Kind) (w l : ℕ) : Representation.Equiv
    (((color k).tprod (weak w)).tprod (leftSpin l))
      (JointSourceExpression.action (.atom ⟨k,w,l,0⟩)) :=
  (Representation.TensorProduct.assoc (color k) (weak w) (leftSpin l)).trans
    ((tensorEquiv (.refl _) (tensorEquiv (.refl _) (rightUnit (leftSpin l) rightZero))).trans
      (atom k w l 0))

def rightPad (k : RestrictedColorWordSupport.Kind) (w r : ℕ) : Representation.Equiv
    (((color k).tprod (weak w)).tprod (rightSpin r))
      (JointSourceExpression.action (.atom ⟨k,w,0,r⟩)) :=
  (Representation.TensorProduct.assoc (color k) (weak w) (rightSpin r)).trans
    ((tensorEquiv (.refl _) (tensorEquiv (.refl _) (leftUnit (rightSpin r) leftZero))).trans
      (atom k w 0 r))

def colorOnly (k : RestrictedColorWordSupport.Kind) : Representation.Equiv (color k)
    (JointSourceExpression.action (.atom ⟨k,0,0,0⟩)) :=
  (rightUnit (color k) weakZero).trans
    ((rightUnit ((color k).tprod (weak 0)) leftZero).trans (leftPad k 0 0))

def weakOnly (w : ℕ) : Representation.Equiv (weak w)
    (JointSourceExpression.action (.atom ⟨.symmetric 0,w,0,0⟩)) :=
  (leftUnit (weak w) colorZero).trans
    ((rightUnit ((color (.symmetric 0)).tprod (weak w)) leftZero).trans (leftPad (.symmetric 0) w 0))

def scalarPair : Representation.Equiv ((color (.symmetric 0)).tprod (weak 0)) (trivial ℂ Group ℂ) :=
  (tensorEquiv colorZero weakZero).trans (Representation.TensorProduct.lid ℂ (trivial ℂ Group ℂ))

def leftOnly (l : ℕ) : Representation.Equiv (leftSpin l)
    (JointSourceExpression.action (.atom ⟨.symmetric 0,0,l,0⟩)) :=
  (leftUnit (leftSpin l) scalarPair).trans (leftPad (.symmetric 0) 0 l)

def rightOnly (r : ℕ) : Representation.Equiv (rightSpin r)
    (JointSourceExpression.action (.atom ⟨.symmetric 0,0,0,r⟩)) :=
  (leftUnit (rightSpin r) scalarPair).trans (rightPad (.symmetric 0) 0 r)

def scalar : Representation.Equiv (trivial ℂ Group ℂ)
    (JointSourceExpression.action (.atom ⟨.symmetric 0,0,0,0⟩)) :=
  colorZero.symm.trans (colorOnly (.symmetric 0))

end
end Math.JointSourceAtoms
