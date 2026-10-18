import Math.LieGroups.SpecialUnitary.Block
import Math.RepresentationTheory.Unitary.FiniteBasisUnitaryModel
import TauCeti.RepresentationTheory.ExteriorPower
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.Basis

/-! Actual defining, dual, and exterior-square representations of SU(n),
with continuous unitary realizations constructed by compact averaging. -/

set_option autoImplicit false

namespace Math.SUN.Matter

noncomputable section

open FiniteBasisHilbertization

abbrev Vector (n : ℕ) := Fin n → ℂ
abbrev Covector (n : ℕ) := Module.Dual ℂ (Vector n)
abbrev Wedge (n : ℕ) := ⋀[ℂ]^2 (Vector n)

def fundamental (n : ℕ) : Representation ℂ (Block.Group n) (Vector n) where
  toFun g := Matrix.toLin' g.val
  map_one' := Matrix.toLin'_one
  map_mul' _ _ := Matrix.toLin'_mul _ _

def antifundamental (n : ℕ) : Representation ℂ (Block.Group n) (Covector n) :=
  (fundamental n).dual

def exteriorTwo (n : ℕ) : Representation ℂ (Block.Group n) (Wedge n) :=
  (fundamental n).exteriorPower 2

def vectorBasis (n : ℕ) : Module.Basis (Fin n) ℂ (Vector n) := Pi.basisFun ℂ (Fin n)
def covectorBasis (n : ℕ) : Module.Basis (Fin n) ℂ (Covector n) := (vectorBasis n).dualBasis
def wedgeBasis (n : ℕ) : Module.Basis (Set.powersetCard (Fin n) 2) ℂ (Wedge n) :=
  (vectorBasis n).exteriorPower 2

theorem fundamental_jointlyContinuous (n : ℕ) :
    Continuous (fun p : Block.Group n × Vector n => fundamental n p.1 p.2) :=
  (continuous_subtype_val.comp continuous_fst).matrix_mulVec continuous_snd

theorem vector_coordinates_continuous (n : ℕ) (i j : Fin n) :
    Continuous (fun g => (vectorBasis n).coord i (fundamental n g (vectorBasis n j))) :=
  ((vectorBasis n).coord i).continuous_of_finiteDimensional.comp
    ((fundamental_jointlyContinuous n).comp (continuous_id.prodMk continuous_const))

theorem covector_coordinates_continuous (n : ℕ) (i j : Fin n) :
    Continuous (fun g => (covectorBasis n).coord i (antifundamental n g (covectorBasis n j))) := by
  simp only [covectorBasis, Module.Basis.coord_apply, Module.Basis.dualBasis_repr]
  exact ((vectorBasis n).dualBasis j).continuous_of_finiteDimensional.comp
    (((fundamental_jointlyContinuous n).comp (continuous_id.prodMk continuous_const)).comp
      continuous_inv)

theorem wedge_coordinates_continuous (n : ℕ) (s t : Set.powersetCard (Fin n) 2) :
    Continuous (fun g => (wedgeBasis n).coord s (exteriorTwo n g (wedgeBasis n t))) := by
  let et := Set.powersetCard.ofFinEmbEquiv.symm t
  let es := Set.powersetCard.ofFinEmbEquiv.symm s
  have he :
      (fun g => (wedgeBasis n).coord s (exteriorTwo n g (wedgeBasis n t))) =
        fun g => (Matrix.of fun i j : Fin 2 =>
          (vectorBasis n).coord (es j) (fundamental n g (vectorBasis n (et i)))).det := by
    funext g
    change ((vectorBasis n).exteriorPower 2).coord s
      (exteriorPower.map 2 (fundamental n g) ((vectorBasis n).exteriorPower 2 t)) = _
    rw [exteriorPower.basis_coord, exteriorPower.basis_apply,
      exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
      exteriorPower.ιMultiDual_apply_ιMulti]
    rfl
  rw [he]
  exact Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
    vector_coordinates_continuous n _ _)

local instance (n : ℕ) : MeasurableSpace (Block.Group n) := borel (Block.Group n)
local instance (n : ℕ) : BorelSpace (Block.Group n) := ⟨rfl⟩

abbrev CovectorHilbert (n : ℕ) := Copy (covectorBasis n)
abbrev WedgeHilbert (n : ℕ) := Copy (wedgeBasis n)

def unitaryDual (n : ℕ) : ContRepresentation ℂ (Block.Group n) (CovectorHilbert n) :=
  FiniteBasisUnitaryModel.model (covectorBasis n) (antifundamental n)
    (covector_coordinates_continuous n)

def unitaryWedge (n : ℕ) : ContRepresentation ℂ (Block.Group n) (WedgeHilbert n) :=
  FiniteBasisUnitaryModel.model (wedgeBasis n) (exteriorTwo n) (wedge_coordinates_continuous n)

def dualEquiv (n : ℕ) : Representation.Equiv (antifundamental n) (unitaryDual n).toRepresentation :=
  FiniteBasisUnitaryModel.modelEquiv _ _ _

def wedgeEquiv (n : ℕ) : Representation.Equiv (exteriorTwo n) (unitaryWedge n).toRepresentation :=
  FiniteBasisUnitaryModel.modelEquiv _ _ _

theorem dual_unitary (n : ℕ) : TauCeti.ContRepresentation.IsUnitary (unitaryDual n) :=
  FiniteBasisUnitaryModel.model_unitary _ _ _

theorem wedge_unitary (n : ℕ) : TauCeti.ContRepresentation.IsUnitary (unitaryWedge n) :=
  FiniteBasisUnitaryModel.model_unitary _ _ _

theorem dual_continuous (n : ℕ) : Continuous (unitaryDual n) :=
  FiniteBasisUnitaryModel.model_continuous _ _ _

theorem wedge_continuous (n : ℕ) : Continuous (unitaryWedge n) :=
  FiniteBasisUnitaryModel.model_continuous _ _ _

end

end Math.SUN.Matter
