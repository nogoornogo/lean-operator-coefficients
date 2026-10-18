import Math.RepresentationTheory.SU2PairExterior
import Math.RepresentationTheory.JointSourceSpinPresentation

/-! Every weak/doublet-spin core exterior degree has a finite joint source
presentation, with either independent spin placement and actual overflow. -/
namespace Math.SU2PairJointPresentation
set_option autoImplicit false
noncomputable section
open Representation JointSourcePresentation SplitRepresentationProjection ExternalInvariantTensor
open scoped TensorProduct

@[reducible] local instance (n : ℕ) : AddCommGroup (Sym[ℂ]^n WeakDoubletScalars.Doublet) :=
  Module.addCommMonoidToAddCommGroup ℂ

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup
    (WeakDoubletScalars.Doublet ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance

def projection (right : Bool) : JointColorSpinWord.Group →* (TauCeti.SU2 × TauCeti.SU2) where
  toFun g := (g.2.1,if right then g.2.2.2 else g.2.2.1)
  map_one' := by cases right <;> rfl
  map_mul' _ _ := by cases right <;> rfl

def pair (right : Bool) (a b : ℕ) : Presentation ((SU2PairExterior.pair a b).comp (projection right)) := by
  refine externalComp (WeakDoubletScalars.doublet.symmetricPower a)
    (WeakDoubletScalars.doublet.symmetricPower b) (projection right) ?_ ?_
  · exact JointSourceSpinPresentation.atWeak a
      ((MonoidHom.fst TauCeti.SU2 TauCeti.SU2).comp (projection right)) (fun _ => rfl)
  · cases right
    · exact JointSourceSpinPresentation.atLeft b
        ((MonoidHom.snd TauCeti.SU2 TauCeti.SU2).comp (projection false)) (fun _ => rfl)
    · exact JointSourceSpinPresentation.atRight b
        ((MonoidHom.snd TauCeti.SU2 TauCeti.SU2).comp (projection true)) (fun _ => rfl)

def two (right : Bool) : Presentation ((SU2PairExterior.tensor.exteriorPower 2).comp (projection right)) :=
  alongEquiv (restrictEquiv (SU2PairExterior.squareEquiv.symm.trans
      (FiniteSourceSums.finTwo SU2PairExterior.squarePiece)) (projection right))
    (sumComp (SU2PairExterior.pair 2 0) (SU2PairExterior.pair 0 2) (projection right)
      (pair right 2 0) (pair right 0 2))

def positive (right : Bool) : (n : ℕ) →
    Presentation ((SU2PairExterior.tensor.exteriorPower n).comp (projection right))
  | 0 => alongEquiv (restrictEquiv SU2PairExterior.zeroEquiv (projection right)) (pair right 0 0)
  | 1 => alongEquiv (restrictEquiv SU2PairExterior.oneEquiv (projection right)) (pair right 1 1)
  | 2 => two right
  | 3 => alongEquiv (restrictEquiv SU2PairExterior.threeEquiv (projection right)) (pair right 1 1)
  | 4 => alongEquiv (restrictEquiv SU2PairExterior.fourEquiv (projection right)) (pair right 0 0)
  | n+5 => zero _ (fun x => exteriorPower.eq_zero_of_finrank_lt (n+5)
      (by rw [SU2PairExterior.tensor_dimension]; omega) x)

end
end Math.SU2PairJointPresentation
