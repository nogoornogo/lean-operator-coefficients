import Physics.FieldTheory.Jets.Lagrangian.YukawaDensitySymmetry
import Physics.FieldTheory.Jets.Lagrangian.RegisteredLagrangianModels
import Math.Algebra.Jets.MixedJetPairCoordinates

/-! Artificial controls of parameter recovery, observable equations and a
deliberately non-scalar spinor product. No finite rank is assumed. -/
namespace Physics.YukawaModelControls
set_option autoImplicit false
noncomputable section
open Math Math.PairedWeylKinetic Math.ScalarWeylYukawa
open scoped TensorProduct
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

theorem free_odd_recovery (kappa massSquared : ℂ) (j : Label) :
    (density kappa massSquared (fun _ => 0) (fun _ => 0)).euler (.inl j) =
      kappa • seed (!j.1,j.2) := by
  simp [ScalarWeylYukawa.generated_odd,oddEquation]

theorem free_scalar_recovery (kappa : ℂ) :
    (density kappa 0 (fun _ => 0) (fun _ => 0)).euler (.inr scalarLabel) = -wave := by
  simp [ScalarWeylYukawa.generated_even,evenEquation]

theorem spectator_equation (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ)
    (j : Label) (hj : j ≠ scalarLabel) :
    (density kappa massSquared mass yukawa).euler (.inr j) = 0 := by
  simp only [ScalarWeylYukawa.generated_even,hj,ite_false]

theorem scalar_target_identity (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ)
    (q : (YukawaModel.model kappa massSquared mass yukawa).Coordinates) :
    (YukawaModel.model kappa massSquared mass yukawa).evaluate q wave+
      massSquared*(YukawaModel.model kappa massSquared mass yukawa).evaluate q phi.eval+
      yukawa false*(YukawaModel.model kappa massSquared mass yukawa).evaluate q (pair false).eval+
      yukawa true*(YukawaModel.model kappa massSquared mass yukawa).evaluate q (pair true).eval = 0 := by
  have h := YukawaModel.scalar_coefficient_equation kappa massSquared mass yukawa
    ((YukawaModel.model kappa massSquared mass yukawa).equivalence.symm q)
  change (YukawaModel.model kappa massSquared mass yukawa).evaluate q
    (evenEquation massSquared yukawa) = 0 at h
  simp only [evenEquation,map_sub,map_neg,map_smul,smul_eq_mul] at h
  change _ = 0
  linear_combination -h

theorem quartic_zero_allows : ∃ q : (RegisteredLagrangianModels.quartic 0).Coordinates,
    (RegisteredLagrangianModels.quartic 0).evaluate q (PolynomialScalarEOM.field^3) = 1 :=
  (RegisteredLagrangianModels.quartic_cubic_value_iff 0 1).mpr (zero_mul _)

theorem quartic_nonzero_forbids : ¬∃ q : (RegisteredLagrangianModels.quartic 1).Coordinates,
    (RegisteredLagrangianModels.quartic 1).evaluate q (PolynomialScalarEOM.field^3) = 1 := by
  rw [RegisteredLagrangianModels.quartic_cubic_value_iff]
  norm_num

def boost : YukawaModel.Group := ⟨!![2,0;0,(1/2:ℂ)],by norm_num [Matrix.det_fin_two]⟩
def nonScalar : A := psi false 0*psi true 0

theorem boost_component (c : Bool) :
    YukawaModel.spin c boost (Pi.single 0 1) = (2:ℂ) • Pi.single 0 1 := by
  cases c
  · ext i; fin_cases i <;>
      norm_num [YukawaModel.spin,boost,WeylSpinor.left,Matrix.mulVec,dotProduct]
  · change WeylSpinor.right boost (Pi.single 0 1) = _
    rw [WeylSpinor.right_apply]
    ext i; fin_cases i <;> norm_num [boost,Matrix.mulVec,dotProduct,map_ofNat]

theorem nonScalar_transform : PairedWeylInput.action boost nonScalar = (4:ℂ) • nonScalar := by
  have hc (c : Bool) : PairedWeylInput.action boost (psi c 0) = (2:ℂ) • psi c 0 := by
    rw [← YukawaModel.zeroOdd_basis c 0,YukawaModel.zeroOdd_covariant,boost_component,map_smul]
  rw [nonScalar,YukawaModel.action_mul,hc,hc,smul_mul_assoc,mul_smul_comm,smul_smul]
  norm_num

def pairProbe : A →ₗ[ℂ] ℂ := TensorProduct.lift {
  toFun x := MixedJetAlgebra.pairCoordinate ((false,0),0) ((true,0),0) x • MvPolynomial.lcoeff ℂ 0
  map_add' x y := by rw [map_add,add_smul]
  map_smul' z x := by
    apply LinearMap.ext
    intro p
    change MixedJetAlgebra.pairCoordinate ((false,0),0) ((true,0),0) (z • x)*p.coeff 0 =
      z*(MixedJetAlgebra.pairCoordinate ((false,0),0) ((true,0),0) x*p.coeff 0)
    rw [map_smul]
    simp only [smul_eq_mul]
    ring }

theorem nonScalar_probe : pairProbe nonScalar = 1 := by
  simp [pairProbe,nonScalar,psi,MixedJetAlgebra.odd,Algebra.TensorProduct.tmul_mul_tmul,
    MixedJetAlgebra.pairCoordinate_ι_mul]

theorem symmetry_breaking_control : PairedWeylInput.action boost nonScalar ≠ nonScalar := by
  intro h
  have he := congrArg pairProbe h
  rw [nonScalar_transform,map_smul,nonScalar_probe] at he
  norm_num at he

end
end Physics.YukawaModelControls
