import Physics.StandardModel.Operators.SMB1ExactMinima
import Physics.StandardModel.Operators.SixQuarkFullSeed
import Physics.StandardModel.Operators.WeinbergFullSeed
import GUT.Common.ProtonProtection.ModelControls
import Physics.StandardModel.Operators.BgwZ6Selection

/-! Conditional consumers on declared three-generation SM/Higgs dictionaries.
No UV-to-light-field, VEV-stabilizer or matching premise is discharged here. -/
namespace GUT.ConditionalInputChecks
set_option autoImplicit false
noncomputable section
open Math SelectionCriteria SMQLPatternRequests

/-- DFPW's supplied pure-baryon cyclic subgroup: q=2,l=0 modulo 18.
This extends the earlier selected-family test to the original all-degree SM input. -/
theorem dfpw_b1_forbidden : OriginalForbidden (2 : ZMod 18) 0
    (fun c => c.1.natAbs=3) :=
  (SMB1ExactMinima.none_iff_forbidden 2 0).mp (by decide +kernel)

/-- The same subgroup forbids the full uR²dR⁴ content at every Higgs count. -/
theorem dfpw_six_forbidden (h d : ℕ) : Forbidden
    (ContentHiggsSupport.Space (2 : ZMod 18) 0 OutsideFamilyHiggsTrials.sixQuarks h d) :=
  (SixQuarkFullSeed.all_forbidden_iff 2 0).mpr (by decide +kernel) h d

/-- LLHH remains allowed under this subgroup alone; no full-stabilizer claim. -/
theorem dfpw_subgroup_weinberg_allowed : Allowed
    (ContentHiggsSupport.Space (2 : ZMod 18) 0 ContentHiggsSupport.leptonPair 2 0) :=
  (WeinbergFullSeed.allowed_iff 2 0 2 0).mpr ⟨rfl,by decide +kernel⟩

/-- Exact light lepton parity; model correspondence is a separate obligation. -/
theorem lepton_parity_b1_forbidden : OriginalForbidden (0 : ZMod 2) 1
    (fun c => c.1.natAbs=3) :=
  (SMB1ExactMinima.none_iff_forbidden 0 1).mp (by decide +kernel)

/-- Applicable to supplied gauge-only split SU5/PS and SM-even Ma inputs.
The grade is twice the physical dimension: twelve means dimension six. -/
theorem trivial_b1_minimum : SMMinimumOperatorDimension.IsMinimum
    (0 : ZMod 2) 0 3 12 :=
  SMB1ExactMinima.exact_of_match 0 0 12 (by decide +kernel) (by decide +kernel)

/-- Integer X=3(B-L), with a charge-six VEV: residual Z6 acts by (q,l)=(1,-3).
This is the product-cover input, not a claimed faithful residual quotient. -/
theorem matter_parity_b1_minimum : SMMinimumOperatorDimension.IsMinimum
    (1 : ZMod 6) (-3) 3 12 :=
  SMB1ExactMinima.exact_of_match 1 (-3) 12 (by decide +kernel) (by decide +kernel)

theorem matter_parity_six_allowed : Allowed
    (ContentHiggsSupport.Space (1 : ZMod 6) (-3) OutsideFamilyHiggsTrials.sixQuarks 0 0) :=
  (SixQuarkFullSeed.allowed_iff 1 (-3) 0 0).mpr ⟨rfl,by decide +kernel⟩

theorem matter_parity_weinberg_allowed : Allowed
    (ContentHiggsSupport.Space (1 : ZMod 6) (-3) ContentHiggsSupport.leptonPair 2 0) :=
  (WeinbergFullSeed.allowed_iff 1 (-3) 2 0).mpr ⟨rfl,by decide +kernel⟩

/-- A Z5 subgroup of unbroken B-L excludes these B-L-violating contents.
This is not an all-sector characterization of continuous B-L. -/
theorem unbroken_bl_six_forbidden (h d : ℕ) : Forbidden
    (ContentHiggsSupport.Space (1 : ZMod 5) (-3) OutsideFamilyHiggsTrials.sixQuarks h d) :=
  (SixQuarkFullSeed.all_forbidden_iff 1 (-3)).mpr (by decide +kernel) h d

theorem unbroken_bl_weinberg_forbidden (h d : ℕ) : Forbidden
    (ContentHiggsSupport.Space (1 : ZMod 5) (-3) ContentHiggsSupport.leptonPair h d) :=
  (WeinbergFullSeed.all_forbidden_iff 1 (-3)).mpr (by decide +kernel) h d

/-- B-L neutrality does not forbid B1: even its chosen Z5 subgroup allows a
minimal dimension-six witness. Full U(1) allowance needs its own invariant map. -/
theorem bl_subgroup_b1_minimum : SMMinimumOperatorDimension.IsMinimum
    (1 : ZMod 5) (-3) 3 12 :=
  SMB1ExactMinima.exact_of_match 1 (-3) 12 (by decide +kernel) (by decide +kernel)

/-- The lepton-parity input also permits the selected B2 and L2 contents. -/
theorem lepton_parity_six_allowed : Allowed
    (ContentHiggsSupport.Space (0 : ZMod 2) 1 OutsideFamilyHiggsTrials.sixQuarks 0 0) :=
  (SixQuarkFullSeed.allowed_iff 0 1 0 0).mpr ⟨rfl,by decide +kernel⟩

theorem lepton_parity_weinberg_allowed : Allowed
    (ContentHiggsSupport.Space (0 : ZMod 2) 1 ContentHiggsSupport.leptonPair 2 0) :=
  (WeinbergFullSeed.allowed_iff 0 1 2 0).mpr ⟨rfl,by decide +kernel⟩

/-- SM external fields in the Ma Z2 input: neutrality does not generate LLHH. -/
theorem sm_even_weinberg_allowed : Allowed
    (ContentHiggsSupport.Space (0 : ZMod 2) 0 ContentHiggsSupport.leptonPair 2 0) :=
  (WeinbergFullSeed.allowed_iff 0 0 2 0).mpr ⟨rfl,by decide +kernel⟩

/-- Proton hexality n=0,p=2,m=5 in DL(T) Eq.(2.17), with the generator
inverted. The restricted physical dictionary coincides with the existing BGW
SM/Higgs dictionary modulo six, including the charged Higgs. -/
theorem proton_hexality_inverse_dictionary :
    (![BgwZ6Selection.fq 0,BgwZ6Selection.fq 1,BgwZ6Selection.fq 2,
       BgwZ6Selection.fq 3,BgwZ6Selection.fq 4,
       BgwZ6Selection.bq 0,BgwZ6Selection.bq 1] : Fin 7 → ZMod 6) =
      ![0,-5,5,2,7,-5,5] := by decide +kernel

end
end GUT.ConditionalInputChecks
