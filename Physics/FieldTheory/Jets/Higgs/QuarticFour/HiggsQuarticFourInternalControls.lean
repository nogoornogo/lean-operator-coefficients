import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInput
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Actual global internal controls for the whole quartic Higgs source.
They provide necessary finite constraints; full-group invariance is separate. -/
namespace Physics.HiggsQuarticFourInternalControls
set_option autoImplicit false
noncomputable section
open Math MvPolynomial DerivativeLiteratureHiggs Matrix
open StandardSMGaugeTensor
abbrev T := HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs
theorem phase_value (y : ℤ) (g : GaugeGroup) : phase y g = (g.2.2 : ℂ)^y := rfl
theorem higgs_apply (g : GaugeGroup) (v : Fin 2 → ℂ) (i : Fin 2) :
    HiggsFieldDictionary.higgs g v i = phase 3 g*
      (∑ a : Fin 2, (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) i a*v a) := rfl
def z : ℂ := (3+4*Complex.I)/5
def phaseCircle : Circle := ⟨z,by
  norm_num [Submonoid.unitSphere,z,Complex.norm_def,Complex.normSq,
    Complex.mul_re,Complex.mul_im]⟩
def phaseWeak : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![(3+4*Complex.I)/5,0;0,(3-4*Complex.I)/5],by
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [mul_apply,Fin.sum_univ_two,star_apply,map_ofNat,Complex.ext_iff,
          Complex.mul_re,Complex.mul_im]
    · norm_num [det_fin_two,Complex.ext_iff,Complex.mul_re,Complex.mul_im]⟩
def phaseGroup : GaugeGroup := (1,phaseWeak,phaseCircle)
theorem phase_forward : phase 3 phaseGroup = z^(3 : ℤ) := rfl
theorem phase_backward : phase 3 (SMGaugeConjugation.conjugate phaseGroup) =
    (star z)^(3 : ℤ) := by
  change (((phaseCircle⁻¹ : Circle) : ℂ))^(3 : ℤ) = (star z)^(3 : ℤ)
  rw [Circle.coe_inv_eq_conj]
  rfl
def rotationWeak : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![(3:ℂ)/5,4/5;-4/5,3/5],by
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [mul_apply,Fin.sum_univ_two,star_apply,map_ofNat]
    · norm_num [det_fin_two]⟩
def rotationGroup : GaugeGroup := (1,rotationWeak,1)
def flipGroup : GaugeGroup := (1,SmallSpecialUnitary.flipTwo,1)

def label : Fin 4 → Label := ![(false,0),(false,1),(true,0),(true,1)]
def weight : Fin 4 → ℤ := ![4,2,-4,-2]
def numerator : Fin 4 → GaussianInt := ![⟨-527,-336⟩,⟨-175,600⟩,⟨-527,336⟩,⟨-175,-600⟩]
def eigen (i : Fin 4) : ℂ := GaussianInt.toComplex (numerator i)/625
def field (i : Fin 4) : A := h (label i).1 (label i).2

theorem label_surjective : Function.Surjective label := by
  rintro ⟨c,a⟩
  cases c <;> fin_cases a
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩

theorem transport_eigen (g : GaugeGroup) (j : Label) (c : ℂ)
    (he : HiggsFieldDictionary.action g (Finsupp.single j 1) = c • Finsupp.single j 1) :
    T g (h j.1 j.2) = c • h j.1 j.2 := by
  rw [← HiggsInternalSymmetry.fields_single,HiggsInternalSymmetry.fields_covariant]
  rw [show PairedComponentFields.action HiggsFieldDictionary.higgs g (Finsupp.single j 1) =
    c • Finsupp.single j 1 from he,map_smul,HiggsInternalSymmetry.fields_single]

theorem phase_action (i : Fin 4) :
    HiggsFieldDictionary.action phaseGroup (Finsupp.single (label i) 1) =
      eigen i • Finsupp.single (label i) 1 := by
  apply HiggsFieldDictionary.components.injective
  rw [HiggsFieldDictionary.components_action,map_smul]
  simp only [HiggsFieldDictionary.components_apply]
  apply Prod.ext <;> funext b
  all_goals simp only [higgs_apply,phase_forward,phase_backward]
  all_goals fin_cases i <;> fin_cases b
  all_goals norm_num [phaseGroup,phaseWeak,phaseCircle,z,label,eigen,numerator,
    weak,SMGaugeConjugation.conjugate,
    SpecialUnitaryContragredient.conjugate,toLin'_apply,mulVec,Fin.sum_univ_two,
    Finsupp.single_apply,Pi.smul_apply,smul_eq_mul,Circle.coe_inv_eq_conj,
    GaussianInt.toComplex,Complex.ext_iff,Complex.mul_re,Complex.mul_im,
    Complex.div_re,Complex.div_im,Matrix.vecHead,Matrix.vecTail,
    pow_succ,map_ofNat,Complex.inv_def,Complex.normSq]

theorem phase_field (i : Fin 4) : T phaseGroup (field i) = eigen i • field i :=
  transport_eigen phaseGroup (label i) (eigen i) (phase_action i)

theorem rotation_action (c : Bool) (a : Fin 2) :
    HiggsFieldDictionary.action rotationGroup (Finsupp.single (c,a) 1) =
      if a = 0 then (3/5 : ℂ) • Finsupp.single (c,0) 1-(4/5 : ℂ) • Finsupp.single (c,1) 1
      else (4/5 : ℂ) • Finsupp.single (c,0) 1+(3/5 : ℂ) • Finsupp.single (c,1) 1 := by
  apply HiggsFieldDictionary.components.injective
  rw [HiggsFieldDictionary.components_action]
  cases c <;> fin_cases a <;> simp only [HiggsFieldDictionary.components_apply]
  all_goals apply Prod.ext <;> funext b
  all_goals fin_cases b
  all_goals norm_num [rotationGroup,rotationWeak,HiggsFieldDictionary.higgs,twist,weak,phase_value,
    SMGaugeConjugation.conjugate,SpecialUnitaryContragredient.conjugate,toLin'_apply,mulVec,
    Fin.sum_univ_two,Finsupp.single_apply,Pi.smul_apply,smul_eq_mul,
    Matrix.vecHead,Matrix.vecTail,map_ofNat]

theorem rotation_field (c : Bool) (a : Fin 2) : T rotationGroup (h c a) =
    if a = 0 then (3/5 : ℂ) • h c 0-(4/5 : ℂ) • h c 1
    else (4/5 : ℂ) • h c 0+(3/5 : ℂ) • h c 1 := by
  rw [← HiggsInternalSymmetry.fields_single (c,a),HiggsInternalSymmetry.fields_covariant]
  rw [show PairedComponentFields.action HiggsFieldDictionary.higgs rotationGroup
      (Finsupp.single (c,a) 1) = _ from rotation_action c a]
  split <;> simp only [map_sub,map_add,map_smul,HiggsInternalSymmetry.fields_single]

end
end Physics.HiggsQuarticFourInternalControls
