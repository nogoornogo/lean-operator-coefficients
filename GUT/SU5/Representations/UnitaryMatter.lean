import GUT.SU5.Representations.Matter
import Math.RepresentationTheory.Unitary.FiniteBasisUnitaryModel
import Mathlib.LinearAlgebra.Dual.Basis

open Math

/-!
# Continuous unitary realizations of five, bar-five, and ten

Each model is equivalent to the actual algebraic SU(5) representation.
Matrix coefficients of the defining/dual actions and minors of the defining
action prove continuity before compact-group unitarization is applied.
The chosen unitary coordinates are not asserted to be the original basis.
-/

set_option autoImplicit false

namespace GUT.SU5.UnitaryMatter

noncomputable section

open StandardModelEmbedding FiniteBasisHilbertization

instance targetMeasurableSpace : MeasurableSpace TargetGroup := borel TargetGroup
instance targetBorelSpace : BorelSpace TargetGroup := ⟨rfl⟩

def fiveBasis : Module.Basis (Fin 5) ℂ Matter.Five := Pi.basisFun ℂ (Fin 5)
def barFiveBasis : Module.Basis (Fin 5) ℂ Matter.BarFive := fiveBasis.dualBasis
def tenBasis : Module.Basis (Set.powersetCard (Fin 5) 2) ℂ Matter.Ten :=
  fiveBasis.exteriorPower 2

theorem fundamental_orbit_continuous (v : Matter.Five) :
    Continuous (fun g => Matter.fundamental g v) :=
  Matter.fundamental_jointlyContinuous.comp (continuous_id.prodMk continuous_const)

theorem five_coordinates_continuous (i j : Fin 5) :
    Continuous (fun g => fiveBasis.coord i (Matter.fundamental g (fiveBasis j))) :=
  (fiveBasis.coord i).continuous_of_finiteDimensional.comp
    (fundamental_orbit_continuous (fiveBasis j))

theorem barFive_coordinates_continuous (i j : Fin 5) :
    Continuous (fun g => barFiveBasis.coord i (Matter.antifundamental g (barFiveBasis j))) := by
  simp only [barFiveBasis, Module.Basis.coord_apply, Module.Basis.dualBasis_repr]
  exact (fiveBasis.dualBasis j).continuous_of_finiteDimensional.comp
    ((fundamental_orbit_continuous (fiveBasis i)).comp continuous_inv)

theorem ten_coordinates_continuous (s t : Set.powersetCard (Fin 5) 2) :
    Continuous (fun g => tenBasis.coord s (Matter.ten g (tenBasis t))) := by
  let et := Set.powersetCard.ofFinEmbEquiv.symm t
  let es := Set.powersetCard.ofFinEmbEquiv.symm s
  have hCoordinate :
      (fun g => tenBasis.coord s (Matter.ten g (tenBasis t))) =
        fun g => (Matrix.of fun i j : Fin 2 =>
          fiveBasis.coord (es j) (Matter.fundamental g (fiveBasis (et i)))).det := by
    funext g
    change (fiveBasis.exteriorPower 2).coord s
      (exteriorPower.map 2 (Matter.fundamental g) (fiveBasis.exteriorPower 2 t)) = _
    rw [exteriorPower.basis_coord, exteriorPower.basis_apply,
      exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
      exteriorPower.ιMultiDual_apply_ιMulti]
    rfl
  rw [hCoordinate]
  apply Continuous.matrix_det
  exact continuous_pi (fun i => continuous_pi (fun j => five_coordinates_continuous _ _))

abbrev FiveHilbert := Copy fiveBasis
abbrev BarFiveHilbert := Copy barFiveBasis
abbrev TenHilbert := Copy tenBasis

def fundamental : ContRepresentation ℂ TargetGroup FiveHilbert :=
  FiniteBasisUnitaryModel.model fiveBasis Matter.fundamental five_coordinates_continuous

def antifundamental : ContRepresentation ℂ TargetGroup BarFiveHilbert :=
  FiniteBasisUnitaryModel.model barFiveBasis Matter.antifundamental barFive_coordinates_continuous

def ten : ContRepresentation ℂ TargetGroup TenHilbert :=
  FiniteBasisUnitaryModel.model tenBasis Matter.ten ten_coordinates_continuous

def fundamentalEquiv : Representation.Equiv Matter.fundamental fundamental.toRepresentation :=
  FiniteBasisUnitaryModel.modelEquiv fiveBasis Matter.fundamental five_coordinates_continuous

def antifundamentalEquiv : Representation.Equiv Matter.antifundamental antifundamental.toRepresentation :=
  FiniteBasisUnitaryModel.modelEquiv barFiveBasis Matter.antifundamental barFive_coordinates_continuous

def tenEquiv : Representation.Equiv Matter.ten ten.toRepresentation :=
  FiniteBasisUnitaryModel.modelEquiv tenBasis Matter.ten ten_coordinates_continuous

theorem fundamental_continuous : Continuous fundamental :=
  FiniteBasisUnitaryModel.model_continuous _ _ _
theorem antifundamental_continuous : Continuous antifundamental :=
  FiniteBasisUnitaryModel.model_continuous _ _ _
theorem ten_continuous : Continuous ten :=
  FiniteBasisUnitaryModel.model_continuous _ _ _

theorem fundamental_unitary : TauCeti.ContRepresentation.IsUnitary fundamental :=
  FiniteBasisUnitaryModel.model_unitary _ _ _
theorem antifundamental_unitary : TauCeti.ContRepresentation.IsUnitary antifundamental :=
  FiniteBasisUnitaryModel.model_unitary _ _ _
theorem ten_unitary : TauCeti.ContRepresentation.IsUnitary ten :=
  FiniteBasisUnitaryModel.model_unitary _ _ _

@[simp] theorem fiveHilbert_finrank : Module.finrank ℂ FiveHilbert = 5 := by
  rw [← fundamentalEquiv.toLinearEquiv.finrank_eq, Matter.five_finrank]
@[simp] theorem barFiveHilbert_finrank : Module.finrank ℂ BarFiveHilbert = 5 := by
  rw [← antifundamentalEquiv.toLinearEquiv.finrank_eq, Matter.barFive_finrank]
@[simp] theorem tenHilbert_finrank : Module.finrank ℂ TenHilbert = 10 := by
  rw [← tenEquiv.toLinearEquiv.finrank_eq, Matter.ten_finrank]

end

end GUT.SU5.UnitaryMatter
