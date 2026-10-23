import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInternalUpper

/-! Actual internal controls on the entire quartic Higgs first-jet source.
One differentiated field is marked; the other three commute. -/
namespace Physics.HiggsFirstInternal
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs HiggsQuarticFourInternalControls
abbrev V := ScalarJetAlgebra.grade (S := Label) (I := Fin 4) 4 1
def mono (i j k l : Fin 4) : A := D 0 (field i)*field j*field k*field l
def K (f : A →ₗ[ℂ] ℂ) (i j k l : Fin 4) : ℂ := f (mono i j k l)
theorem K_apply (f : A →ₗ[ℂ] ℂ) (i j k l : Fin 4) :
    K f i j k l = f (D 0 (field i)*field j*field k*field l) := rfl

theorem mono_grade (i j k l : Fin 4) : mono i j k l ∈ V := by
  have he (i : Fin 4) : field i ∈ ScalarJetAlgebra.grade (S := Label) (I := Fin 4) 1 0 :=
    HiggsQuarticFourInput.h_grade _ _
  exact (((ScalarJetAlgebra.totalDerivative_mem 0 (he i)).mul (he j)).mul (he k)).mul (he l)

def ordered (j k l : Fin 4) : Fin 3 → Fin 4 :=
  if j ≤ k then
    if k ≤ l then ![j,k,l] else if j ≤ l then ![j,l,k] else ![l,j,k]
  else if j ≤ l then ![k,j,l] else if k ≤ l then ![k,l,j] else ![l,k,j]

theorem normalize (f : A →ₗ[ℂ] ℂ) (i j k l : Fin 4) :
    K f i j k l = K f i (ordered j k l 0) (ordered j k l 1) (ordered j k l 2) := by
  unfold ordered
  split_ifs <;> apply congrArg f <;> dsimp [mono] <;> ring

theorem vanish (f : A →ₗ[ℂ] ℂ)
    (hI : ∀ g i j k l, f (T g (mono i j k l)) = f (mono i j k l))
    (i j k l : Fin 4) (hw : weight i+weight j+weight k+weight l ≠ 0) :
    K f i j k l = 0 := by
  have he := hI phaseGroup i j k l
  simp only [mono,map_mul,HiggsInternalSymmetry.derivative_commute,phase_field,
    Derivation.map_smul,smul_mul_assoc,mul_smul_comm,smul_smul,map_smul,smul_eq_mul] at he
  have hz : (eigen i*eigen j*eigen k*eigen l-1)*K f i j k l = 0 := by
    dsimp only [K,mono]
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (HiggsQuarticFourInternalUpper.eigen_nontrivial i j k l hw)

def normalK (f : A →ₗ[ℂ] ℂ) (i j k l : Fin 4) : ℂ :=
  if weight i+weight j+weight k+weight l = 0 then
    K f i (ordered j k l 0) (ordered j k l 1) (ordered j k l 2) else 0

theorem normal_form (f : A →ₗ[ℂ] ℂ)
    (hI : ∀ g i j k l, f (T g (mono i j k l)) = f (mono i j k l)) (i j k l : Fin 4) :
    K f i j k l = normalK f i j k l := by
  unfold normalK
  split_ifs with hw
  · exact normalize f i j k l
  · exact vanish f hI i j k l hw

theorem rotation_value (f : A →ₗ[ℂ] ℂ)
    (hI : ∀ g i j k l, f (T g (mono i j k l)) = f (mono i j k l)) (i j k l : Fin 4) :
    f (D 0 (HiggsQuarticFourInternalUpper.rotateField i)*
      HiggsQuarticFourInternalUpper.rotateField j*HiggsQuarticFourInternalUpper.rotateField k*
        HiggsQuarticFourInternalUpper.rotateField l) - K f i j k l = 0 := by
  have he := hI rotationGroup i j k l
  simp only [mono,map_mul,HiggsInternalSymmetry.derivative_commute,
    HiggsQuarticFourInternalUpper.rotation_field4] at he
  exact sub_eq_zero.mpr he

end
end Physics.HiggsFirstInternal
