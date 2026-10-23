import Math.Algebra.Jets.MixedJetAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold

/-! Removing positive odd jets in the full exterior algebra. The target is
still an exterior algebra, so fermionic signs are preserved. -/
namespace Math.MixedJetConstantOdd
set_option autoImplicit false
noncomputable section
open JetLinear ScalarJetAlgebra
attribute [local instance] Classical.propDecidable
variable {F I : Type*}

def residue : Jet F I →ₗ[ℂ] JetLinear.Field F :=
  Finsupp.linearCombination ℂ (fun j => if j.2 = 0 then Finsupp.single j.1 1 else 0)

@[simp] theorem residue_single (j : Index F I) (c : ℂ) :
    residue (Finsupp.single j c) = if j.2 = 0 then Finsupp.single j.1 c else 0 := by
  classical
  by_cases h : j.2 = 0 <;> simp [residue,h]

theorem residue_shift (i : I) (v : Jet F I) : residue (JetLinear.shift i v) = 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw,add_zero]
  | single j c =>
    have hn : j.2 + Finsupp.single i 1 ≠ 0 := by
      intro he
      have hi := congrArg (fun a : I →₀ ℕ => a i) he
      simp at hi
    simp [ScalarJetAlgebra.shift,hn]

def project : MixedJetAlgebra.Odd F I →ₐ[ℂ] ExteriorAlgebra ℂ (JetLinear.Field F) :=
  ExteriorAlgebra.map residue

@[simp] theorem project_ι (v : Jet F I) :
    project (ExteriorAlgebra.ι ℂ v) = ExteriorAlgebra.ι ℂ (residue v) :=
  ExteriorAlgebra.map_apply_ι _ _

theorem project_derivative (i : I) (x : MixedJetAlgebra.Odd F I) :
    project (MixedJetAlgebra.oddDerivative i x) = 0 := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => simp [MixedJetAlgebra.oddDerivative]
  | add x y hx hy => simp only [map_add,hx,hy,add_zero]
  | ι_mul x v hx =>
    simp [MixedJetAlgebra.oddDerivative,ExteriorAlgebra.derivationOfLinear_mul,
      ExteriorAlgebra.derivationOfLinear_ι,residue_shift,
      show project (ExteriorAlgebra.derivationOfLinear (JetLinear.shift i) x) = 0 from hx]

end
end Math.MixedJetConstantOdd
