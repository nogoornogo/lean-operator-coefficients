import Math.LieGroups.Spin.HalfSpin
import Math.LieGroups.Spin.SU5Inclusion

/-! The full Fock action of actual compact Spin elements conjugates Clifford
generators according to the actual orthogonal projection. -/

set_option autoImplicit false

namespace Math.CompactSpin.Fock

noncomputable section

open Polarized

abbrev Space (n : ℕ) := ExteriorAlgebra ℂ (HalfSpin.polarization n).W

def algebraAction (n : ℕ) : CliffordAlgebra (realForm n) →ₐ[ℝ] Module.End ℂ (Space n) :=
  ((TauCeti.spinAction (complexForm n) (HalfSpin.polarization n)).restrictScalars ℝ).comp
    (cliffordMap n)

def representation (n : ℕ) : Representation ℂ (Group (n + n)) (Space n) :=
  (algebraAction n).toRingHom.toMonoidHom.comp
    ((Units.coeHom _).comp spinGroup.toUnits)

theorem coefficient_continuous (n : ℕ) (l : Module.Dual ℂ (Space n)) (v : Space n) :
    Continuous (fun g : Group (n + n) => l (representation n g v)) := by
  let c : CliffordAlgebra (realForm n) →ₗ[ℝ] ℂ :=
    (l.restrictScalars ℝ).comp
      (((LinearMap.applyₗ v).restrictScalars ℝ).comp (algebraAction n).toLinearMap)
  exact c.continuous_of_finiteDimensional.comp continuous_subtype_val

def generator (n : ℕ) : RealSpace n →ₗ[ℝ] Module.End ℂ (Space n) :=
  (algebraAction n).toLinearMap.comp (CliffordAlgebra.ι (realForm n))

theorem conjugation (n : ℕ) (g : Group (n + n)) (v : RealSpace n) :
    representation n g * generator n v * representation n g⁻¹ =
      generator n (CliffordAlgebra.spinVectorAction (realForm n) g v) := by
  have hi : ((g⁻¹ : Group (n + n)) : CliffordAlgebra (realForm n)) =
      star (g : CliffordAlgebra (realForm n)) := by
    rw [← spinGroup.star_eq_inv, spinGroup.coe_star]
  change algebraAction n g * algebraAction n (CliffordAlgebra.ι (realForm n) v) *
    algebraAction n (g⁻¹ : Group (n + n)) =
      algebraAction n (CliffordAlgebra.ι (realForm n)
        (CliffordAlgebra.spinVectorAction (realForm n) g v))
  rw [hi, ← map_mul, ← map_mul, CliffordAlgebra.ι_spinVectorAction_apply]

theorem SU5_vectorAction (g : SU5) (v : RealSpace 5) :
    CliffordAlgebra.spinVectorAction (realForm 5) (SU5Inclusion g) v =
      SpecialUnitaryRealification.realAction g v := by
  have h := DFunLike.congr_fun projection_comp_SU5Inclusion g
  have hv := congrArg (fun f : Orthogonal 10 => f.val v) h
  calc
    _ = (projection 10 (SU5Inclusion g)).val v := by
      simp only [projection, CliffordAlgebra.realCliffordSpinDoubleCoverZero_rightHom,
        CliffordAlgebra.coe_spinToSpecialOrthogonal_apply]
    _ = (realification g).val v := hv
    _ = _ := rfl

theorem SU5_conjugation (g : SU5) (v : RealSpace 5) :
    representation 5 (SU5Inclusion g) * generator 5 v *
      representation 5 (SU5Inclusion g)⁻¹ =
        generator 5 (SpecialUnitaryRealification.realAction g v) := by
  rw [conjugation, SU5_vectorAction]

theorem halfSpin_restriction (n : ℕ) (g : Group (n + n)) (s : HalfSpin.Space n) :
    (HalfSpin.representation n g s : Space n) = representation n g s := by
  change (TauCeti.spinPlusAction (complexForm n) (HalfSpin.polarization n)
    (TauCeti.splitEvenPolarization_line ℂ n) (evenMap n (TauCeti.spinGroupToEven (realForm n) g)) s :
      Space n) = _
  rw [TauCeti.coe_spinPlusAction_apply]
  rfl

end

end Math.CompactSpin.Fock
