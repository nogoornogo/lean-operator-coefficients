import Math.Algebra.Jets.JetDirections
import Math.RepresentationTheory.Jets.MixedJetSource

/-! Functorial scalar and mixed actions on the actual jet presentations.
The input maps act on jet generators, so directions may mix. -/
namespace Math.JetFunctor
set_option autoImplicit false
noncomputable section
open JetLinear ScalarJetAlgebra
open scoped TensorProduct

variable {S T U F B I : Type*}

@[reducible] local instance : AddCommGroup (ScalarJetAlgebra.Algebra S I) := inferInstance
@[reducible] local instance : Module ℂ (ScalarJetAlgebra.Algebra S I) := inferInstance
@[reducible] local instance : AddCommGroup (MixedJetAlgebra.Algebra F B I) := inferInstance
@[reducible] local instance : Module ℂ (MixedJetAlgebra.Algebra F B I) := inferInstance

def polynomialMap (L : Jet S I →ₗ[ℂ] Jet T I) :
    ScalarJetAlgebra.Algebra S I →ₐ[ℂ] ScalarJetAlgebra.Algebra T I :=
  MvPolynomial.aeval (fun j => linearForm (L (Finsupp.single j 1)))

@[simp] theorem polynomialMap_X (L : Jet S I →ₗ[ℂ] Jet T I) (j : Index S I) :
    polynomialMap L (MvPolynomial.X j) = linearForm (L (Finsupp.single j 1)) := by
  simp [polynomialMap]

theorem polynomialMap_linearForm (L : Jet S I →ₗ[ℂ] Jet T I) (v : Jet S I) :
    polynomialMap L (linearForm v) = linearForm (L v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c =>
    simp only [show Finsupp.single j c = c • Finsupp.single j (1 : ℂ) by simp,
      map_smul, linearForm, Finsupp.linearCombination_single, one_smul, polynomialMap_X]

@[simp] theorem polynomialMap_id :
    polynomialMap (LinearMap.id : Jet S I →ₗ[ℂ] Jet S I) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [linearForm]

theorem polynomialMap_comp (L : Jet S I →ₗ[ℂ] Jet T I) (M : Jet T I →ₗ[ℂ] Jet U I) :
    polynomialMap (M.comp L) = (polynomialMap M).comp (polynomialMap L) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [polynomialMap_linearForm]

def polynomialAction {H : Type*} [Monoid H] (ρ : Representation ℂ H (Jet S I)) :
    Representation ℂ H (ScalarJetAlgebra.Algebra S I) where
  toFun h := (polynomialMap (ρ h)).toLinearMap
  map_one' := by rw [ρ.map_one]; change (polynomialMap LinearMap.id).toLinearMap = _
                 rw [polynomialMap_id]; rfl
  map_mul' h k := by rw [ρ.map_mul]; exact congrArg AlgHom.toLinearMap (polynomialMap_comp _ _)

theorem polynomial_covariant [Fintype I] {H : Type*} [Monoid H]
    (ρ : Representation ℂ H (Jet S I)) (h : H) (i : I) (c : I → ℂ)
    (hc : ∀ v, ρ h (JetLinear.shift i v) = ∑ j, c j • JetLinear.shift j (ρ h v))
    (p : ScalarJetAlgebra.Algebra S I) :
    polynomialAction ρ h (totalDerivative i p) =
      ∑ j, c j • totalDerivative j (polynomialAction ρ h p) := by
  change polynomialMap (ρ h) (totalDerivative i p) =
    ∑ j, c j • totalDerivative j (polynomialMap (ρ h) p)
  induction p using MvPolynomial.induction_on with
  | C a => simp [polynomialMap]
  | add p q hp hq => simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p x hp =>
    change polynomialMap (ρ h) (totalDerivative i (p * MvPolynomial.X x)) = _
    rw [totalDerivative_mul, map_add, map_mul, map_mul, totalDerivative_X,
      polynomialMap_X, polynomialMap_X]
    have hx : linearForm (ρ h (Finsupp.single (ScalarJetAlgebra.shift i x) 1)) =
        ∑ j, c j • totalDerivative j (linearForm (ρ h (Finsupp.single x 1))) := by
      rw [← JetLinear.shift_single, hc, map_sum]
      simp only [map_smul, derivative_linearForm]
    rw [hx]
    simp only [map_mul, polynomialMap_X]
    rw [hp, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [totalDerivative_mul, smul_add, mul_smul_comm]

def mixedAction {H : Type*} [Monoid H]
    (ρF : Representation ℂ H (Jet F I)) (ρB : Representation ℂ H (Jet B I)) :
    Representation ℂ H (MixedJetAlgebra.Algebra F B I) :=
  ρF.exteriorAlgebra.tprod (polynomialAction ρB)

theorem mixedAction_one {H : Type*} [Monoid H]
    (ρF : Representation ℂ H (Jet F I)) (ρB : Representation ℂ H (Jet B I)) (h : H) :
    mixedAction ρF ρB h 1 = 1 := by
  simp [mixedAction, Algebra.TensorProduct.one_def, polynomialAction]

theorem mixedAction_mul {H : Type*} [Monoid H]
    (ρF : Representation ℂ H (Jet F I)) (ρB : Representation ℂ H (Jet B I)) (h : H)
    (p q : MixedJetAlgebra.Algebra F B I) :
    mixedAction ρF ρB h (p * q) = mixedAction ρF ρB h p * mixedAction ρF ρB h q := by
  induction p using TensorProduct.inductionOn with
  | add p r hp hr => simp only [add_mul, map_add, hp, hr]
  | tmul x y =>
    induction q using TensorProduct.inductionOn with
    | add q r hq hr => simp only [mul_add, map_add, hq, hr]
    | tmul z w =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      change ExteriorAlgebra.map (ρF h) (x * z) ⊗ₜ[ℂ] polynomialMap (ρB h) (y * w) = _
      simp only [map_mul, mixedAction, Representation.tprod_apply, TensorProduct.map_tmul,
        polynomialAction, Algebra.TensorProduct.tmul_mul_tmul]
      rfl

theorem mixed_covariant [Fintype I] {H : Type*} [Monoid H]
    (ρF : Representation ℂ H (Jet F I)) (ρB : Representation ℂ H (Jet B I))
    (h : H) (i : I) (c : I → ℂ)
    (hF : ∀ v, ρF h (JetLinear.shift i v) = ∑ j, c j • JetLinear.shift j (ρF h v))
    (hB : ∀ v, ρB h (JetLinear.shift i v) = ∑ j, c j • JetLinear.shift j (ρB h v))
    (p : MixedJetAlgebra.Algebra F B I) :
    mixedAction ρF ρB h (MixedJetAlgebra.totalDerivative i p) =
      ∑ j, c j • MixedJetAlgebra.totalDerivative j (mixedAction ρF ρB h p) := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]
  | tmul x y =>
    simp only [MixedJetAlgebra.totalDerivative_tmul, map_add, mixedAction,
      Representation.tprod_apply, TensorProduct.map_tmul]
    rw [show ρF.exteriorAlgebra h (MixedJetAlgebra.oddDerivative i x) =
        ∑ j, c j • MixedJetAlgebra.oddDerivative j (ρF.exteriorAlgebra h x) from
      ExteriorAlgebra.exteriorAlgebra_derivationOfLinear ρF h JetLinear.shift i c hF x,
      polynomial_covariant ρB h i c hB y]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, ← Finset.sum_add_distrib,
      smul_add]

def oddVector : Jet F I →ₗ[ℂ] MixedJetAlgebra.Algebra F B I :=
  ((TensorProduct.mk ℂ (MixedJetAlgebra.Odd F I) (MixedJetAlgebra.Even B I)).flip 1).comp
    (ExteriorAlgebra.ι ℂ)

def evenVector : Jet B I →ₗ[ℂ] MixedJetAlgebra.Algebra F B I :=
  (TensorProduct.mk ℂ (MixedJetAlgebra.Odd F I) (MixedJetAlgebra.Even B I) 1).comp linearForm

@[simp] theorem oddVector_single (j : Index F I) (c : ℂ) :
    oddVector (B := B) (Finsupp.single j c) = c • MixedJetAlgebra.odd j := by
  rw [show Finsupp.single j c = c • Finsupp.single j (1 : ℂ) by simp, map_smul]
  rfl

@[simp] theorem evenVector_single (j : Index B I) (c : ℂ) :
    evenVector (F := F) (Finsupp.single j c) = c • MixedJetAlgebra.even j := by
  simp [evenVector, linearForm, MixedJetAlgebra.even]

theorem oddVector_mem {d : ℕ} {v : Jet F I} (hv : v ∈ JetDirections.jetOrder F I d) :
    oddVector (B := B) v ∈ MixedJetAlgebra.grade F B I 1 0 d := by
  rw [← Finsupp.sum_single v, map_finsuppSum]
  apply Submodule.sum_mem
  intro j hj
  change oddVector (B := B) (Finsupp.single j (v j)) ∈ _
  rw [oddVector_single]
  have he : order j.2 = d := hv hj
  exact Submodule.smul_mem _ _ (he ▸ MixedJetAlgebra.odd_mem j)

theorem evenVector_mem {d : ℕ} {v : Jet B I} (hv : v ∈ JetDirections.jetOrder B I d) :
    evenVector (F := F) v ∈ MixedJetAlgebra.grade F B I 0 1 d := by
  rw [← Finsupp.sum_single v, map_finsuppSum]
  apply Submodule.sum_mem
  intro j hj
  change evenVector (F := F) (Finsupp.single j (v j)) ∈ _
  rw [evenVector_single]
  have he : order j.2 = d := hv hj
  exact Submodule.smul_mem _ _ (he ▸ MixedJetAlgebra.even_mem j)

end
end Math.JetFunctor
