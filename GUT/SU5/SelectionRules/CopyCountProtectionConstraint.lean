import GUT.SU5.SelectionRules.MatrixTenMass
import Math.RepresentationTheory.Protection.ProtectionConstraintPullback

open Physics

/-! Necessary copy-count constraints for the existing scalar-ten matrix family. -/
namespace GUT.SU5.CopyCountProtectionConstraint
set_option autoImplicit false
noncomputable section
open Math Representation Math.SelectionCriteria MatrixTenMass
variable {H : Type*} [CommGroup H] {p q : ℕ}

local instance (A : Matrices p q) (K : Kernels A) : AddCommGroup (QuarkSpace A K) := inferInstance
local instance (A : Matrices p q) (K : Kernels A) : AddCommGroup (UpSpace A K) := inferInstance
local instance (A : Matrices p q) (K : Kernels A) : AddCommGroup (ElectronSpace A K) := inferInstance

/-- Vanishing on every certified participating light range is required for
full B1 prohibition; no equality with the full B1 domain is asserted. -/
def ParticipatingForbidden (chi : H →* Circle) (A : Matrices p q) : Prop :=
  ∀ K : Kernels A, Forbidden
    (QqueSpinorExterior.ExteriorCoefficient (quarkRho chi A K)
      (upLeftRho chi A K).dual (electronLeftRho chi A K).dual)

/-- Matrix entries are unrestricted; the positive copy surplus is sufficient. -/
theorem source_le_target (chi : H →* Circle) (A : Matrices p q)
    (hf : ParticipatingForbidden chi A) : p ≤ q := by
  by_contra hn
  have h : q < p := Nat.lt_of_not_ge hn
  obtain ⟨f,hne⟩ := exists_actual_exterior chi A (kernels A h)
  exact hne (hf (kernels A h) f)

theorem surplus_excludes (chi : H →* Circle) (A : Matrices p q) (h : q < p) :
    ¬ ParticipatingForbidden chi A :=
  fun hf => (Nat.not_le_of_gt h) (source_le_target chi A hf)

/-- Counts may vary over a parameter family; no count dictionary is supplied. -/
theorem parameter_retain {I : Type*} (sources targets : I → ℕ)
    (chi : H →* Circle) (matrices : ∀ i, Matrices (sources i) (targets i))
    (sm : I → Prop) (i : I) (hs : sm i)
    (hp : ParticipatingForbidden chi (matrices i)) :
    ProtectionConstraintPullback.retain sm (fun _ => True)
      (fun i => sources i ≤ targets i) i :=
  ⟨hs, fun _ => source_le_target chi (matrices i) hp⟩

/-- Every allowed matrix choice at the old two-versus-one control is excluded. -/
theorem two_one_excluded (chi : H →* Circle) (A : Matrices 2 1) :
    ¬ ParticipatingForbidden chi A := surplus_excludes chi A (by decide)

/-- Balanced counts can still leave light modes; the inequality is not sufficient. -/
def balancedZero : Matrices 1 1 := ⟨0,0,0⟩

def balancedKernel : Kernels balancedZero where
  up := fun _ => 1
  quark := fun _ => 1
  electron := fun _ => 1
  up_ne := by intro h; have he := congrFun h 0; norm_num at he
  quark_ne := by intro h; have he := congrFun h 0; norm_num at he
  electron_ne := by intro h; have he := congrFun h 0; norm_num at he
  up_zero := by simp [matrixMap,balancedZero]
  quark_zero := by simp [matrixMap,balancedZero]
  electron_zero := by simp [matrixMap,balancedZero]

theorem balanced_counts_not_sufficient (chi : H →* Circle) :
    (1 : ℕ) ≤ 1 ∧ ¬ ParticipatingForbidden chi balancedZero := by
  refine ⟨by decide, ?_⟩
  intro hf
  obtain ⟨f,hne⟩ := exists_actual_exterior chi balancedZero balancedKernel
  exact hne (hf balancedKernel f)

end
end GUT.SU5.CopyCountProtectionConstraint
