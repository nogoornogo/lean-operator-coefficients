import Math.RepresentationTheory.JointSourceSpinPresentation
import TauCeti.RepresentationTheory.ExteriorPower

/-! Colorless single-spin cores in the joint source syntax, with both
independent spin placements and symbolic overflow exclusion. -/
namespace Math.SU2SingleJointPresentation
set_option autoImplicit false
noncomputable section
open Representation JointSourcePresentation SplitRepresentationProjection
open scoped TensorProduct

def projection : Bool → JointColorSpinWord.Group →* TauCeti.SU2
  | false => JointSourceAtoms.leftProjection
  | true => JointSourceAtoms.rightProjection

def one (right : Bool) : Presentation (WeakDoubletScalars.doublet.comp (projection right)) := by
  cases right
  · exact JointSourceSpinPresentation.leftDoublet (projection false) (fun _ => rfl)
  · exact JointSourceSpinPresentation.rightDoublet (projection true) (fun _ => rfl)

def top : Representation.Equiv (WeakDoubletScalars.doublet.exteriorPower 2) (trivial ℂ TauCeti.SU2 ℂ) where
  toLinearEquiv := exteriorPower.topEquiv (Pi.basisFun ℂ (Fin 2))
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have hd : LinearMap.det (WeakDoubletScalars.doublet g) = 1 := by
      change LinearMap.det (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) ℂ)) = 1
      rw [LinearMap.det_toLin']
      exact g.prop.2
    change exteriorPower.topEquiv (Pi.basisFun ℂ (Fin 2))
      (exteriorPower.map 2 (WeakDoubletScalars.doublet g) x) = exteriorPower.topEquiv (Pi.basisFun ℂ (Fin 2)) x
    rw [exteriorPower.map_top_eq_det_smul (Pi.basisFun ℂ (Fin 2)),hd,one_smul]
    rfl

def positive (right : Bool) : (n : ℕ) →
    Presentation ((WeakDoubletScalars.doublet.exteriorPower n).comp (projection right))
  | 0 => alongEquiv (restrictEquiv WeakDoubletScalars.doublet.exteriorPowerZeroEquiv (projection right))
      (JointSourceSpinPresentation.scalarComp (projection right))
  | 1 => alongEquiv (restrictEquiv WeakDoubletScalars.doublet.exteriorPowerOneEquiv (projection right)) (one right)
  | 2 => alongEquiv (restrictEquiv top (projection right)) (JointSourceSpinPresentation.scalarComp (projection right))
  | n+3 => zero _ (fun x => exteriorPower.eq_zero_of_finrank_lt (n+3) (by
      change Module.finrank ℂ (Fin 2 → ℂ) < n+3
      rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
      omega) x)

end
end Math.SU2SingleJointPresentation
