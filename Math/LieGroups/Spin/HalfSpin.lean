import Math.LieGroups.Spin.PolarizedClifford
import TauCeti.RepresentationTheory.Spin.Dimension
import Math.RepresentationTheory.Unitary.FiniteBasisUnitaryModel
import Mathlib.RepresentationTheory.Character

/-! Half-spin modules restricted to actual compact Spin(2n).
The even exterior model has dimension 16 at n = 5. SU(5) branching and
irreducibility of the compact restriction are separate claims. -/

set_option autoImplicit false

namespace Math.CompactSpin.HalfSpin

noncomputable section

open Polarized

abbrev polarization (n : ℕ) := TauCeti.splitEvenPolarization ℂ n
abbrev Space (n : ℕ) := TauCeti.spinPlus (complexForm n) (polarization n)

def algebraAction (n : ℕ) : CliffordAlgebra.even (realForm n) →ₐ[ℝ]
    Module.End ℂ (Space n) :=
  ((TauCeti.spinPlusAction (complexForm n) (polarization n)
    (TauCeti.splitEvenPolarization_line ℂ n)).restrictScalars ℝ).comp (evenMap n)

def representation (n : ℕ) : Representation ℂ (Group (n + n)) (Space n) :=
  (algebraAction n).toRingHom.toMonoidHom.comp (TauCeti.spinGroupToEven (realForm n))

theorem polarization_finrank (n : ℕ) : Module.finrank ℂ (polarization n).W = n := by
  simpa using Module.finrank_eq_card_basis (TauCeti.splitEvenBasis ℂ n)

theorem finrank (n : ℕ) (hn : 0 < n) : Module.finrank ℂ (Space n) = 2 ^ (n - 1) := by
  have hW : (polarization n).W ≠ ⊥ := by
    intro h
    have := polarization_finrank n
    rw [h, finrank_bot] at this
    omega
  rw [TauCeti.finrank_spinPlus (polarization n) hW, polarization_finrank]

theorem finrank_sixteen : Module.finrank ℂ (Space 5) = 16 := by
  simpa using finrank 5 (by norm_num)

theorem coefficient_continuous (n : ℕ) (l : Module.Dual ℂ (Space n)) (v : Space n) :
    Continuous (fun g : Group (n + n) => l (representation n g v)) := by
  let c : (CliffordAlgebra.even (realForm n)).toSubmodule →ₗ[ℝ] ℂ :=
    (l.restrictScalars ℝ).comp
      (((LinearMap.applyₗ v).restrictScalars ℝ).comp (algebraAction n).toLinearMap)
  exact c.continuous_of_finiteDimensional.comp (continuous_subtype_val.subtype_mk _)

def basis (n : ℕ) : Module.Basis (Fin (Module.finrank ℂ (Space n))) ℂ (Space n) :=
  Module.finBasis ℂ (Space n)

abbrev HilbertSpace (n : ℕ) := FiniteBasisHilbertization.Copy (basis n)

local instance (n : ℕ) : MeasurableSpace (Group (n + n)) := borel _
local instance (n : ℕ) : BorelSpace (Group (n + n)) := ⟨rfl⟩

def unitaryModel (n : ℕ) : ContRepresentation ℂ (Group (n + n)) (HilbertSpace n) :=
  FiniteBasisUnitaryModel.model (basis n) (representation n)
    (fun i j => coefficient_continuous n ((basis n).coord i) (basis n j))

theorem unitaryModel_unitary (n : ℕ) :
    TauCeti.ContRepresentation.IsUnitary (unitaryModel n) :=
  FiniteBasisUnitaryModel.model_unitary _ _ _

theorem unitaryModel_continuous (n : ℕ) :
    Continuous (fun p : Group (n + n) × HilbertSpace n => unitaryModel n p.1 p.2) :=
  FiniteBasisUnitaryModel.model_jointlyContinuous _ _ _

def unitaryModelEquiv (n : ℕ) :
    Representation.Equiv (representation n) (unitaryModel n).toRepresentation :=
  FiniteBasisUnitaryModel.modelEquiv _ _ _

theorem unitaryModel_character (n : ℕ) :
    (unitaryModel n).toRepresentation.character = (representation n).character :=
  (Representation.char_iso (unitaryModelEquiv n)).symm

theorem hilbert_finrank_sixteen : Module.finrank ℂ (HilbertSpace 5) = 16 :=
  (FiniteBasisHilbertization.Copy.valLinearEquiv (basis 5)).finrank_eq.trans finrank_sixteen

def centralNegOne : Group 10 :=
  CliffordAlgebra.spinGroup.negOne (realForm 5)
    (TauCeti.nondegenerate_realCliffordForm 10 0).ne_zero

theorem projection_centralNegOne : projection 10 centralNegOne = 1 := by
  simp [projection, centralNegOne]

theorem representation_centralNegOne : representation 5 centralNegOne = -1 := by
  have h : TauCeti.spinGroupToEven (realForm 5) centralNegOne = -1 := by
    apply Subtype.ext
    simp [centralNegOne]
  change algebraAction 5 _ = -1
  exact (congrArg (algebraAction 5) h).trans
    ((map_neg (algebraAction 5) 1).trans (congrArg Neg.neg (map_one (algebraAction 5))))

/-- The compact representation is genuinely spinorial: it does not factor
through the SO(10) projection. -/
theorem not_descends_to_SO :
    ¬ ∃ rho : Representation ℂ (Orthogonal 10) (Space 5),
      representation 5 = rho.comp (projection 10) := by
  rintro ⟨rho, h⟩
  have he := DFunLike.congr_fun h centralNegOne
  rw [representation_centralNegOne] at he
  have hm : (-1 : Module.End ℂ (Space 5)) = 1 := by
    simpa only [MonoidHom.comp_apply, projection_centralNegOne, map_one] using he
  let : Nontrivial (Space 5) := Module.nontrivial_of_finrank_pos (by rw [finrank_sixteen]; decide)
  obtain ⟨v, hv⟩ := exists_ne (0 : Space 5)
  have hv' : -v = v := LinearMap.congr_fun hm v
  have ht : (2 : ℂ) • v = 0 := by
    calc
      _ = v + v := by module
      _ = -v + v := congrArg (fun x => x + v) hv'.symm
      _ = 0 := neg_add_cancel v
  exact hv ((smul_eq_zero.mp ht).resolve_left (by norm_num))

theorem character_centralNegOne : (representation 5).character centralNegOne = -16 := by
  rw [Representation.character, representation_centralNegOne]
  calc
    _ = -LinearMap.trace ℂ (Space 5) 1 := map_neg (LinearMap.trace ℂ (Space 5)) 1
    _ = -16 := by rw [LinearMap.trace_one, finrank_sixteen]; norm_num

theorem unitary_character_centralNegOne :
    (unitaryModel 5).toRepresentation.character centralNegOne = -16 := by
  rw [unitaryModel_character, character_centralNegOne]

end

end Math.CompactSpin.HalfSpin
