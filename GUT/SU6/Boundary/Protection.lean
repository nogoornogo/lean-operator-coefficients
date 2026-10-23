import GUT.SU6.Boundary.Interactions
import GUT.SU6.SelectionRules.Models.CyclicProtectionFeasibility
import Physics.StandardModel.Operators.Selection.BaryonParitySelection

/-! The actual boundary charges connect to existing coefficient inputs.
Boundary amplitudes are constructed; identification with analytic mixed modes
remains a separate certificate, not an assumption smuggled into the construction. -/
namespace GUT.SU6BoundaryProtection
set_option autoImplicit false
noncomputable section
open Math Physics StandardSMGaugeTensor SMEpsilonTensor StandardSMExterior
open SU6BoundaryBaryon

/-- The left Q and ec are actual vectors in Λ²6. -/
def left15 (x : SU6BoundarySelection.Light15) : SU6BoundaryCube.Square :=
  StandardSMExterior.algebraicEquiv.symm (SU6BoundarySelection.embed15 x)

theorem left15_residual (z : Circle) (x : SU6BoundarySelection.Light15) :
    defining.exteriorPower 2 z (left15 x) = left15 ((z : ℂ)^2 • x.1,x.2) := by
  apply StandardSMExterior.branch_bijective.1
  rw [branch_action]
  change blocksAction z (StandardSMExterior.algebraicEquiv
    (StandardSMExterior.algebraicEquiv.symm _)) =
    StandardSMExterior.algebraicEquiv (StandardSMExterior.algebraicEquiv.symm _)
  rw [StandardSMExterior.algebraicEquiv.apply_symm_apply,
    StandardSMExterior.algebraicEquiv.apply_symm_apply,left15_charges]

theorem left15_gauge (g : GaugeGroup) (x : SU6BoundarySelection.Light15) :
    StandardSMExterior.exteriorRho g (left15 x) =
      left15 ((quark.prod electronRight.dual) g x) := by
  have h := Representation.IntertwiningMap.isIntertwining _ _
    StandardSMExterior.algebraicEquiv.toIntertwiningMap g (left15 x)
  apply StandardSMExterior.branch_bijective.1
  change branch (StandardSMExterior.exteriorRho g (left15 x)) = blocksRho g (branch (left15 x)) at h
  rw [h]
  change blocksRho g (StandardSMExterior.algebraicEquiv
    (StandardSMExterior.algebraicEquiv.symm _)) =
    StandardSMExterior.algebraicEquiv (StandardSMExterior.algebraicEquiv.symm _)
  rw [StandardSMExterior.algebraicEquiv.apply_symm_apply,
    StandardSMExterior.algebraicEquiv.apply_symm_apply,SU6BoundarySelection.embed15_covariant]

theorem right6_residual (z : Circle) (x : Color × Weak) :
    splitAction z (SU6BoundarySelection.embed6Right x) =
      SU6BoundarySelection.embed6Right ((z : ℂ)^2 • x.1,x.2) := rfl

/-- The weak conjugate of the right six is the usual physical left lepton. -/
def lepton_dictionary : Representation.Equiv lepton (twist weak 3).dual :=
  Physics.StandardSMContragredient.leptonDualEquiv

/-- All selected quarks have C4 charge 2; leptons and the sterile mode have charge 0. -/
theorem finite_right20_charge (g : CyclicCharge.Group 4) (x : Color) :
    defining.exteriorPower 3 (finitePhase g) (SU6BoundaryCube.embed x) =
      ZMod.stdAddChar ((2 : ZMod 4)*Multiplicative.toAdd g) • SU6BoundaryCube.embed x := by
  rw [right20_charge,finite_quark_phase]

/-- A familiar bounded, three-generation coefficient input now has a boundary source. -/
theorem bounded_light_forbidden :
    SelectionCriteria.Forbidden (SU6ProtectionFeasibility.LightSector (2 : ZMod 4) 0) := by
  apply (InverseCyclicSMCharges.three_generation_forbidden_iff _ _).mpr
  change (6 : ZMod 4) ≠ 0
  exact BaryonParitySelection.nonneutral_b1 (b := 3) rfl

/-- Removing the protecting action restores an actual nonzero bounded coefficient. -/
theorem neutral_control :
    SelectionCriteria.Allowed (SU6ProtectionFeasibility.LightSector (0 : ZMod 4) 0) :=
  (InverseCyclicSMCharges.three_generation_allowed_iff _ _).mpr (by simp)

/-- All degrees, arbitrary multiplicity spaces and arbitrary Higgs multiplicities. -/
theorem all_degree_b1
    {F : DeltaLOneSignedInput.Species → Type*}
    [∀ u, AddCommGroup (F u)] [∀ u, Module ℂ (F u)]
    {S : BnvMixedInput.ScalarSpecies → Type*}
    [∀ u, AddCommGroup (S u)] [∀ u, Module ℂ (S u)] :
    ∀ n m, ∀ f : ComposableBLSupport.Input
      (BaryonParitySelection.flavor (F := F)) (BaryonParitySelection.scalarFlavor (S := S))
      BaryonParitySelection.target n m, f = 0 := BaryonParitySelection.all_forbidden

/-- Any independently supplied mixed-mode/source identification may be transported.
This does not construct a Dirac zero-mode or a KK-spectrum certificate. -/
theorem transport_forbidden {C : Type*} [AddCommGroup C] [Module ℂ C]
    (e : C ≃ₗ[ℂ] SU6ProtectionFeasibility.LightSector (2 : ZMod 4) 0) :
    SelectionCriteria.Forbidden C := by
  intro c
  apply e.injective
  rw [bounded_light_forbidden (e c),map_zero]

end
end GUT.SU6BoundaryProtection
