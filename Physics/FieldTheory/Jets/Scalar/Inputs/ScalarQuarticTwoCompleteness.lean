import Math.Algebra.Constructions.ScalarDegreeTwo
import Physics.FieldTheory.Jets.Lorentz.LorentzFiniteControls
import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureScalar
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Complete four-field/two-derivative Lorentz coefficient vanishing.
An arbitrary linear extension is only used as notation on the fixed grade;
no invariant or relation-preserving extension is assumed. -/
namespace Physics.ScalarQuarticTwoCompleteness
set_option autoImplicit false
noncomputable section
open Math MvPolynomial ScalarJetAlgebra PolynomialScalarEOM
abbrev V := grade (S := Unit) (I := Fin 4) 4 2
abbrev P := ScalarDerivativeInterface.scalar 0
abbrev Dir := JetDirections.Direction (Fin 4)

def linearFirst : Dir →ₗ[ℂ] OffShell :=
  ∑ i : Fin 4, (Finsupp.lapply i).smulRight (D i field)

theorem linearFirst_apply (u : Dir) : linearFirst u = ∑ i : Fin 4, u i • D i field := by
  simp [linearFirst]
@[simp] theorem linearFirst_single (i : Fin 4) : linearFirst (Finsupp.single i 1) = D i field := by
  simp [linearFirst,Finsupp.single_apply]

theorem linearFirst_covariant (g : LorentzDirections.Group) (u : Dir) :
    offAction g (linearFirst u) = linearFirst (LorentzDirections.direction g u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | single i c =>
    have he : Finsupp.single i c = c • Finsupp.single i (1 : ℂ) := by simp
    simp only [he,map_smul,linearFirst_single]
    congr 1
    rw [linearFirst_apply]
    exact (derivative_covariance g i field).trans (by rw [field_invariant])

theorem field_grade : field ∈ grade (S := Unit) (I := Fin 4) 1 0 := by
  change (X ((),0) : OffShell).IsWeightedHomogeneous weight (1,0)
  simpa [weight,order] using isWeightedHomogeneous_X ℂ weight ((),(0 : Fin 4 →₀ ℕ))

theorem field_power_grade (n : ℕ) : field^n ∈ grade (S := Unit) (I := Fin 4) n 0 := by
  change (field^n).IsWeightedHomogeneous weight (n,0)
  simpa using field_grade.pow n

theorem first_grade (i : Fin 4) : D i field ∈ grade (S := Unit) (I := Fin 4) 1 1 :=
  totalDerivative_mem i field_grade

theorem linearFirst_grade (u : Dir) : linearFirst u ∈ grade (S := Unit) (I := Fin 4) 1 1 := by
  rw [linearFirst_apply]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (first_grade i))

theorem product_grade (u v : Dir) : field^2*linearFirst u*linearFirst v ∈ V :=
  ((field_power_grade 2).mul (linearFirst_grade u)).mul (linearFirst_grade v)

theorem stable : ∀ g, V ≤ V.comap (P.action g) := by
  intro g p hp
  exact JetFunctor.polynomialMap_homogeneous _
    (JetDirections.combined_order LorentzJetIBP.scalarField LorentzDirections.direction g) hp

def selected := P.select V stable

variable (f : OffShell →ₗ[ℂ] ℂ)
  (hInv : ∀ g p, p ∈ V → f (offAction g p) = f p)
  (hRel : ∀ p, p ∈ P.relations → p ∈ V → f p = 0)

def bilinear : Dir →ₗ[ℂ] Dir →ₗ[ℂ] ℂ where
  toFun u := {
    toFun v := f (field^2*linearFirst u*linearFirst v)
    map_add' v w := by simp [map_add,mul_add]
    map_smul' c v := by simp [map_smul] }
  map_add' u v := by ext w; simp [map_add,mul_add,add_mul]
  map_smul' c u := by ext v; simp [map_smul]

@[simp] theorem bilinear_apply (u v : Dir) : bilinear f u v = f (field^2*linearFirst u*linearFirst v) := rfl

include hInv in
theorem bilinear_invariant (g : LorentzDirections.Group) (u v : Dir) :
    bilinear f (LorentzDirections.direction g u) (LorentzDirections.direction g v) = bilinear f u v := by
  have h := hInv g (field^2*linearFirst u*linearFirst v) (product_grade u v)
  change f (field^2*linearFirst (LorentzDirections.direction g u)*
    linearFirst (LorentzDirections.direction g v)) = f (field^2*linearFirst u*linearFirst v)
  simpa only [map_mul,map_pow,field_invariant,linearFirst_covariant] using h

include hRel in
theorem trace : bilinear f (LorentzFiniteControls.E 0) (LorentzFiniteControls.E 0)-
    bilinear f (LorentzFiniteControls.E 1) (LorentzFiniteControls.E 1)-
    bilinear f (LorentzFiniteControls.E 2) (LorentzFiniteControls.E 2)-
    bilinear f (LorentzFiniteControls.E 3) (LorentzFiniteControls.E 3) = 0 := by
  have he : DerivativeLiteratureScalar.twoDerivative =
      field^2*(D 0 field)*(D 0 field)-field^2*(D 1 field)*(D 1 field)-
        field^2*(D 2 field)*(D 2 field)-field^2*(D 3 field)*(D 3 field) := by
    rw [DerivativeLiteratureScalar.twoDerivative,LorentzJetIBP.kinetic_formula]
    simp [field,MasslessScalarEOM.field,D,ScalarJetAlgebra.shift]
    ring
  have hm (i : Fin 4) : field^2*D i field*D i field ∈ V := by
    simpa only [LorentzFiniteControls.E,linearFirst_single] using
      product_grade (LorentzFiniteControls.E i) (LorentzFiniteControls.E i)
  have hmem : DerivativeLiteratureScalar.twoDerivative ∈ V := by
    rw [he]
    exact V.sub_mem (V.sub_mem (V.sub_mem (hm 0) (hm 1)) (hm 2)) (hm 3)
  have hv := hRel DerivativeLiteratureScalar.twoDerivative
    ((Submodule.Quotient.mk_eq_zero _).mp DerivativeLiteratureScalar.two_projection_zero) hmem
  rw [he,map_sub,map_sub,map_sub] at hv
  simpa only [bilinear_apply,LorentzFiniteControls.E,linearFirst_single] using hv

include hInv hRel in
theorem first_product_zero (i j : Fin 4) : f (field^2*D i field*D j field) = 0 := by
  have h := LorentzFiniteControls.trace_zero (bilinear f) (bilinear_invariant f hInv) (trace f hRel) i j
  simpa only [bilinear_apply,LorentzFiniteControls.E,linearFirst_single] using h

include hInv hRel in
theorem second_product_zero (i j : Fin 4) : f (field^3*D i (D j field)) = 0 := by
  have hm : field^3*D j field ∈ grade (S := Unit) (I := Fin 4) 4 1 :=
    (field_power_grade 3).mul (first_grade j)
  have hd := hRel (D i (field^3*D j field))
    (Submodule.mem_sup_right (DifferentialEquation.derivative_mem_ibp D i _))
    (totalDerivative_mem i hm)
  have he : D i (field^3*D j field) =
      (3 : ℂ) • (field^2*D i field*D j field)+field^3*D i (D j field) := by
    simp [pow_succ,MvPolynomial.smul_eq_C_mul]
    norm_num only [map_ofNat]
    ring
  rw [he,map_add,map_smul,first_product_zero f hInv hRel,smul_zero,zero_add] at hd
  exact hd

include hInv hRel in
theorem monomial_zero {a : Index Unit (Fin 4) →₀ ℕ}
    (ha : Finsupp.weight weight a = (4,2)) (c : ℂ) : f (monomial a c) = 0 := by
  have hm : (monomial a c : OffShell) = c • monomial a 1 := by simp [smul_monomial]
  rw [hm,map_smul]
  suffices h : f (monomial a 1) = 0 by rw [h,smul_zero]
  rcases ScalarDegreeTwo.exponent_quartic_two ha with ⟨i,j,he⟩ | ⟨i,j,he⟩
  · rw [he,monomial_add_single,← X_pow_eq_monomial]
    simp only [pow_one]
    have hx : (X (ScalarDegreeTwo.second i j) : OffShell) = D j (D i field) := by
      simp [ScalarDegreeTwo.second,field,MasslessScalarEOM.field,D,shift]
    rw [hx]
    exact second_product_zero f hInv hRel j i
  · rw [he,monomial_add_single,monomial_add_single,← X_pow_eq_monomial]
    simp only [pow_one]
    have hx (i : Fin 4) : (X (ScalarDegreeTwo.first i) : OffShell) = D i field := by
      simp [ScalarDegreeTwo.first,field,MasslessScalarEOM.field,D,shift]
    rw [hx,hx]
    exact first_product_zero f hInv hRel i j

include hInv hRel in
theorem whole_grade_zero (p : V) : f p.val = 0 := by
  have he := congrArg f p.val.as_sum
  rw [map_sum] at he
  rw [he]
  apply Finset.sum_eq_zero
  intro a ha
  exact monomial_zero f hInv hRel (p.property (MvPolynomial.mem_support_iff.mp ha)) _

theorem selected_forbidden (F : selected.Coefficient) : F = 0 := by
  obtain ⟨f,hf⟩ := F.val.toLinearMap.exists_extend
  have he (p : OffShell) (hp : p ∈ V) : f p = F.val ⟨p,hp⟩ :=
    LinearMap.congr_fun hf ⟨p,hp⟩
  have hi : ∀ g p, p ∈ V → f (offAction g p) = f p := by
    intro g p hp
    rw [he p hp,he (offAction g p) (stable g hp)]
    exact F.val.isIntertwining _ _ g ⟨p,hp⟩
  have hr : ∀ p, p ∈ P.relations → p ∈ V → f p = 0 := by
    intro p hp hV
    rw [he p hV]
    exact F.property hp
  apply Subtype.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro p
  change F.val p = 0
  rw [← he p.val p.property]
  exact whole_grade_zero f hi hr p

theorem coefficient_dimension : Module.finrank ℂ selected.Coefficient = 0 := by
  have : Subsingleton selected.Coefficient :=
    ⟨fun a b => (selected_forbidden a).trans (selected_forbidden b).symm⟩
  exact Module.finrank_zero_of_subsingleton

end
end Physics.ScalarQuarticTwoCompleteness
