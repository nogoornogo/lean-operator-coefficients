import Physics.StandardModel.Operators.ComposableBLSupport
import Physics.StandardModel.Operators.WeinbergSMInterface
import Math.LinearAlgebra.MixedSelectionRequests

/-! Printed parity restricted to SM/Higgs, not the inert-eta alphabet. -/
namespace GUT.DevMohapatraParity
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput
abbrev H := CyclicCharge.Group 2

def chi (g : H) : AddChar (ℤ × ℤ) ℂ where
  toFun q := MixedChargeSelection.cyclicCharacter g (q.1 : ZMod 2)
  map_zero_eq_one' := by simp
  map_add_eq_mul' q r := by simp [AddChar.map_add_eq_mul]

def copies {V : Type*} [AddCommGroup V] [Module ℂ V] (q : ℤ × ℤ) : Representation ℂ H V where
  toFun g := LinearMap.lsmul ℂ V (chi g q)
  map_one' := by ext; simp [chi, MixedChargeSelection.cyclicCharacter]
  map_mul' g h := by
    ext v
    simp [chi, MixedChargeSelection.cyclicCharacter, mul_add,
      AddChar.map_add_eq_mul, smul_smul, mul_comm]

variable {F : Species → Type*} [∀ u, AddCommGroup (F u)] [∀ u, Module ℂ (F u)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ u, AddCommGroup (S u)] [∀ u, Module ℂ (S u)]

def flavor (u : Species) : Representation ℂ H (F u) := copies (ComposableBLSupport.fermionCharge u)
def scalarFlavor (u : BnvMixedInput.ScalarSpecies) : Representation ℂ H (S u) :=
  copies (ComposableBLSupport.bosonCharge u)

theorem detect (q : ℤ × ℤ) (hq : q.1.natAbs = 3) : ∃ g, chi g q ≠ 1 := by
  apply (MixedChargeSelection.cyclic_detect_iff (q.1 : ZMod 2)).mpr
  intro hz
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd q.1 2).mp hz
  omega

theorem all_bOne_forbidden : ∀ n m,
    ∀ f : ComposableBLSupport.Input (flavor (F := F)) (scalarFlavor (S := S))
      (fun q => q.1.natAbs = 3) n m, f = 0 := by
  apply ComposableBLSupport.forbidden _ _ _ chi
  · intro g u v; rfl
  · intro g u v; rfl
  · intro n m p s ht; exact detect _ ht

/-- Residual phases for left lepton and SM Higgs are actually neutral. -/
theorem lepton_trivial : flavor (F := fun _ => ℂ) 3 = trivial ℂ H ℂ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  simp [flavor, copies, chi, ComposableBLSupport.fermionCharge, baryon,
    MixedChargeSelection.cyclicCharacter]

theorem higgs_trivial : scalarFlavor (S := fun _ => ℂ) 0 = trivial ℂ H ℂ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  simp [scalarFlavor, copies, chi, ComposableBLSupport.bosonCharge,
    MixedChargeSelection.cyclicCharacter]

abbrev LLHH := WeinbergSMInterface.ModelSector (flavor (F := fun _ => ℂ) 3)

theorem llhh_allowed : SelectionCriteria.Allowed LLHH := by
  change SelectionCriteria.Allowed (WeinbergSMInterface.ModelSector (flavor (F := fun _ => ℂ) 3))
  rw [lepton_trivial]
  let e := WeinbergSMInterface.oneGenerationEquiv (R := H)
  refine ⟨e.symm 1, ?_⟩
  intro hz
  have he := congrArg e hz
  simp at he
end
end GUT.DevMohapatraParity
