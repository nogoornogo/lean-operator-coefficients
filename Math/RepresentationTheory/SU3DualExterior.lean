import Math.RepresentationTheory.SU3DefiningExterior

/-! Determinant-one volume and degree-two duality for the dual defining
color action. No real identification of color with its dual is made. -/
namespace Math.SU3DualExterior
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior

abbrev rho := SU3DefiningExterior.rho.dual
abbrev Vector := Module.Dual ℂ SU3DefiningExterior.Vector

def basis := SU3DefiningExterior.basis.dualBasis

theorem determinant (g : Group) : LinearMap.det (rho g)=1 := by
  change LinearMap.det (SU3DefiningExterior.rho g⁻¹).dualMap=1
  rw [LinearMap.det_dualMap,SU3DefiningExterior.determinant]

def volume := exteriorPower.topEquiv (Module.finBasis ℂ Vector)

def twoEquiv : Representation.Equiv (rho.exteriorPower 2) SU3DefiningExterior.rho :=
  ((ComplementaryExteriorDuality.equiv rho determinant volume (by
      rw [Subspace.dual_finrank_eq,SU3DefiningExterior.dimension])).trans
    (SplitRepresentationProjection.dualEquiv rho.exteriorPowerOneEquiv)).trans
      (SplitRepresentationProjection.bidualEquiv SU3DefiningExterior.rho).symm

def topEquiv : Representation.Equiv (rho.exteriorPower 3) (trivial ℂ Group ℂ) where
  toLinearEquiv := exteriorPower.topEquiv basis
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change exteriorPower.topEquiv basis (exteriorPower.map 3 (rho g) x)=exteriorPower.topEquiv basis x
    rw [exteriorPower.map_top_eq_det_smul basis,determinant g,one_smul]
    rfl

end
end Math.SU3DualExterior
