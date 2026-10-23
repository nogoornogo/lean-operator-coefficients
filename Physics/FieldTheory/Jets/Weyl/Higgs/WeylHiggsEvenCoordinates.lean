import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsEvenValue

/-! Internal invariance and the actual IBP row turn candidate evaluation
into a complete test for all marked Higgs first-jet coordinates. -/
namespace Physics.WeylHiggsEvenValue
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput
open WeylHiggsInternalLift

theorem S_value (f : A →ₗ[ℂ] ℂ) (h : ∀ g p, p ∈ V → f (action g p) = f p) :
    S f = 3*(HiggsFirstInternal.K (scalarFunctional f) 0 0 2 2-
      HiggsFirstInternal.K (scalarFunctional f) 2 0 0 2) := by
  let ell := scalarFunctional f
  have hi := scalar_invariant f h
  simp only [S,Fin.sum_univ_two]
  change (HiggsFirstInternal.K ell 0 2 2 0-HiggsFirstInternal.K ell 2 0 2 0+
    (HiggsFirstInternal.K ell 0 2 3 1-HiggsFirstInternal.K ell 2 0 3 1))+
    ((HiggsFirstInternal.K ell 1 3 2 0-HiggsFirstInternal.K ell 3 1 2 0)+
      (HiggsFirstInternal.K ell 1 3 3 1-HiggsFirstInternal.K ell 3 1 3 1)) =
        3*(HiggsFirstInternal.K ell 0 0 2 2-HiggsFirstInternal.K ell 2 0 0 2)
  simp only [HiggsFirstInternal.normal_form ell hi]
  norm_num [HiggsFirstInternal.normalK,HiggsFirstInternal.ordered,HiggsQuarticFourInternalControls.weight,
    HiggsFirstInternal.value0123 ell hi,HiggsFirstInternal.value1023 ell hi,
    HiggsFirstInternal.value1133 ell hi,HiggsFirstInternal.value2013 ell hi,
    HiggsFirstInternal.value3012 ell hi,HiggsFirstInternal.value3113 ell hi]
  ring

theorem candidate_coordinates (f : A →ₗ[ℂ] ℂ) (h : ∀ g p, p ∈ V → f (action g p) = f p) :
    f DerivativeLiteratureMixed.candidate = (24*Complex.I)*
      (HiggsFirstInternal.K (scalarFunctional f) 0 0 2 2-
        HiggsFirstInternal.K (scalarFunctional f) 2 0 0 2) := by
  rw [candidate_value_raw f h,S_value f h]
  ring

theorem coordinates_zero (f : A →ₗ[ℂ] ℂ) (h : ∀ g p, p ∈ V → f (action g p) = f p)
    (hRel : input.relations ≤ f.ker) (hF : f DerivativeLiteratureMixed.candidate = 0) :
    HiggsFirstInternal.K (scalarFunctional f) 0 0 2 2 = 0 ∧
      HiggsFirstInternal.K (scalarFunctional f) 2 0 0 2 = 0 := by
  have hv := candidate_coordinates f h
  rw [hF] at hv
  have hd : HiggsFirstInternal.K (scalarFunctional f) 0 0 2 2-
      HiggsFirstInternal.K (scalarFunctional f) 2 0 0 2 = 0 :=
    (mul_eq_zero.mp hv.symm).resolve_left (mul_ne_zero (by norm_num : (24 : ℂ) ≠ 0) Complex.I_ne_zero)
  have hr := radial_relation f h hRel
  constructor
  · linear_combination (1/2 : ℂ)*hr+(1/2 : ℂ)*hd
  · linear_combination (1/2 : ℂ)*hr-(1/2 : ℂ)*hd

theorem all_scalar_zero (f : A →ₗ[ℂ] ℂ) (h : ∀ g p, p ∈ V → f (action g p) = f p)
    (hRel : input.relations ≤ f.ker) (hF : f DerivativeLiteratureMixed.candidate = 0)
    (i j k l : Fin 4) : HiggsFirstInternal.K (scalarFunctional f) i j k l = 0 := by
  obtain ⟨h0,h2⟩ := coordinates_zero f h hRel hF
  exact HiggsFirstInternal.all_zero (scalarFunctional f) (scalar_invariant f h) h0 h2 i j k l

end
end Physics.WeylHiggsEvenValue
