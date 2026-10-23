import Math.Algebra.Constructions.ScalarWeylYukawa
import Math.Algebra.Constructions.MixedScalarInclusion
import Math.RepresentationTheory.Lagrangian.LagrangianModel
import Physics.FieldTheory.Jets.Weyl.Equations.PairedWeylGeneratedInput
import Physics.FieldTheory.Jets.Higgs.Inputs.HiggsLagrangianInput

/-! A complete algebraic scalar/Majorana-type Yukawa input on the existing
paired source, with actual SL(2,C), independent complexified conjugate labels
and ordinary derivatives. Three unused even components remain spectators. -/
namespace Physics.YukawaModel
set_option autoImplicit false
noncomputable section
open Math
open Math.LocalPolynomial hiding D
open Math.LocalPolynomial.Expr Math.PairedWeylKinetic Math.ScalarWeylYukawa
open Math.JetLinear Math.JetDirections
open scoped TensorProduct
abbrev Group := LorentzDirections.Group
abbrev Spinor := WeylSpinor.Space
abbrev Equations := WeylLinearEquation.Equations
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

theorem action_mul (g : Group) (u v : A) :
    PairedWeylInput.action g (u*v) = PairedWeylInput.action g u*PairedWeylInput.action g v :=
  JetFunctor.mixedAction_mul PairedWeylInput.jets PairedWeylInput.bosons g u v

def spin (c : Bool) : Representation ℂ Group Spinor :=
  if c then WeylSpinor.right else WeylSpinor.left

def raise (f : Equations) : Spinor :=
  fun i => if i=0 then -f (Pi.single 1 1) else f (Pi.single 0 1)

theorem raise_pair (f : Equations) (v : Spinor) : SMEpsilonTensor.eps2 (raise f) v = -f v := by
  have hv : v = v 0 • Pi.single 0 (1:ℂ)+v 1 • Pi.single 1 (1:ℂ) := by
    ext i; fin_cases i <;> simp
  conv_rhs => rw [hv,map_add,map_smul,map_smul]
  simp [SMEpsilonTensor.eps2,raise,smul_eq_mul]
  ring

theorem spin_pair (c : Bool) (g : Group) (u v : Spinor) :
    SMEpsilonTensor.eps2 (spin c g u) (spin c g v) = SMEpsilonTensor.eps2 u v := by
  cases c
  · exact SMEpsilonTensor.eps2_invariant _ g.property u v
  · exact SMEpsilonTensor.eps2_invariant _ (WeylSpinor.conjugate g).property u v

theorem raise_covariant (c : Bool) (g : Group) (f : Equations) :
    spin c g (raise f) = raise ((spin c).dual g f) := by
  have he (v : Spinor) : SMEpsilonTensor.eps2 (spin c g (raise f)) v =
      SMEpsilonTensor.eps2 (raise ((spin c).dual g f)) v := by
    have h := spin_pair c g (raise f) (spin c g⁻¹ v)
    rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply] at h
    rw [h,raise_pair,raise_pair]
    rfl
  funext i
  fin_cases i
  · simpa [SMEpsilonTensor.eps2] using he (Pi.single 1 1)
  · have h := he (Pi.single 0 1)
    simpa [SMEpsilonTensor.eps2] using h

def zeroOdd (c : Bool) : Spinor →ₗ[ℂ] A :=
  (PairedWeylInput.oddInc c).comp ((atOrder 0).comp LorentzJetIBP.spinorBasis.symm.toLinearMap)

theorem zeroOdd_basis (c : Bool) (a : Fin 2) : zeroOdd c (Pi.single a 1) = psi c a := by
  have he : LorentzJetIBP.spinorBasis.symm (Pi.single a (1:ℂ)) = Finsupp.single a 1 := by
    apply LorentzJetIBP.spinorBasis.injective
    simp [LorentzJetIBP.spinorBasis]
  simp only [zeroOdd,LinearMap.comp_apply,LinearEquiv.coe_coe,he,atOrder_single]
  rw [PairedWeylInput.oddInc,LinearMap.comp_apply,PairedWeylInput.jetInc_single,
    JetFunctor.oddVector_single,one_smul]
  rfl

theorem zeroOdd_covariant (c : Bool) (g : Group) (v : Spinor) :
    PairedWeylInput.action g (zeroOdd c v) = zeroOdd c (spin c g v) := by
  simp only [zeroOdd,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [PairedWeylInput.oddInc_covariant,combined_zero]
  congr 2

theorem raise_row (c : Bool) (a : Fin 2) :
    zeroOdd c (raise (WeylLinearEquation.row a)) = epsilon c a := by
  fin_cases a
  · change zeroOdd c (raise (WeylLinearEquation.row 0)) = epsilon c 0
    have h : raise (WeylLinearEquation.row 0) = Pi.single 1 (1:ℂ) := by
      ext i; fin_cases i <;> simp [raise,WeylLinearEquation.row]
    rw [h,zeroOdd_basis]; rfl
  · change zeroOdd c (raise (WeylLinearEquation.row 1)) = epsilon c 1
    have h : raise (WeylLinearEquation.row 1) = -Pi.single 0 (1:ℂ) := by
      ext i; fin_cases i <;> simp [raise,WeylLinearEquation.row]
    rw [h,map_neg,zeroOdd_basis]; rfl

theorem even_transport (g : Group) (p : ScalarJetAlgebra.Algebra Label (Fin 4)) :
    PairedWeylInput.action g (MixedScalarInclusion.embed p) =
      MixedScalarInclusion.embed (HiggsLagrangianInput.transport g p) := by
  change JetFunctor.mixedAction PairedWeylInput.jets PairedWeylInput.bosons g _ = _
  rw [MixedScalarInclusion.natural]
  have he : PairedWeylInput.bosons g = jetMap (S := Label) (LorentzDirections.direction g) :=
    combined_trivial LorentzDirections.direction g
  change MixedScalarInclusion.embed (JetFunctor.polynomialMap (PairedWeylInput.bosons g) p) = _
  rw [he]
  rfl

theorem phi_invariant (g : Group) : PairedWeylInput.action g phi.eval = phi.eval := by
  change PairedWeylInput.action g (MixedScalarInclusion.embed (DerivativeLiteratureHiggs.h false 0)) = _
  rw [even_transport,HiggsLagrangianInput.field_invariant]
  rfl

theorem wave_invariant (g : Group) : PairedWeylInput.action g wave = wave := by
  have he : wave = MixedScalarInclusion.embed
      (DerivativeLiteratureHiggs.box (DerivativeLiteratureHiggs.h false 0)) := by
    simp only [wave,DerivativeLiteratureHiggs.box,map_sub,← MixedScalarInclusion.derivative]
    rfl
  rw [he,even_transport,HiggsLagrangianInput.wave_invariant g (false,0)]

theorem zeroOdd_expand (c : Bool) (v : Spinor) :
    zeroOdd c v = v 0 • psi c 0+v 1 • psi c 1 := by
  have hv : v = v 0 • Pi.single 0 (1:ℂ)+v 1 • Pi.single 1 (1:ℂ) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hv,map_add,map_smul,map_smul,zeroOdd_basis,zeroOdd_basis]

theorem zeroOdd_product (c : Bool) (u v : Spinor) :
    zeroOdd c u*zeroOdd c v = SMEpsilonTensor.eps2 u v • (pair c).eval := by
  have hs (a : Fin 2) : psi c a*psi c a = 0 := by
    simpa only [psi,pow_two] using MixedJetAlgebra.odd_square (B := Label) ((c,a),0)
  have ht : psi c 1*psi c 0 = -(psi c 0*psi c 1) := by
    simpa [psi] using MixedJetParity.odd_slide ((c,1),0) (psi c 0)
  rw [zeroOdd_expand,zeroOdd_expand]
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul,hs,ht,
    smul_zero,zero_add,add_zero,smul_neg,pair,spinor,fermion,eval_mul]
  rw [add_comm,mul_comm (v 1) (u 0),mul_comm (v 0) (u 1),← sub_eq_add_neg,← sub_smul]
  rfl

theorem pair_invariant (c : Bool) (g : Group) :
    PairedWeylInput.action g (pair c).eval = (pair c).eval := by
  change PairedWeylInput.action g (psi c 0*psi c 1) = _
  rw [action_mul]
  rw [← zeroOdd_basis c 0,← zeroOdd_basis c 1,zeroOdd_covariant,zeroOdd_covariant,
    zeroOdd_product,spin_pair]
  simp [SMEpsilonTensor.eps2]

def massMap (c : Bool) : Equations →ₗ[ℂ] A where
  toFun f := zeroOdd c (raise f)
  map_add' f h := by
    have he : raise (f+h) = raise f+raise h := by ext i; fin_cases i <;> simp [raise,add_comm]
    rw [he,map_add]
  map_smul' z f := by
    have he : raise (z • f) = z • raise f := by ext i; fin_cases i <;> simp [raise]
    simp only [he,map_smul,RingHom.id_apply]

def kineticMap (c : Bool) : Equations →ₗ[ℂ] A :=
  if c then PairedWeylInput.leftSeed else PairedWeylInput.rightSeed

theorem kineticMap_covariant (c : Bool) (g : Group) (f : Equations) :
    PairedWeylInput.action g (kineticMap c f) = kineticMap c ((spin c).dual g f) := by
  cases c
  · exact PairedWeylInput.right_covariant g f
  · exact PairedWeylInput.left_covariant g f

theorem massMap_covariant (c : Bool) (g : Group) (f : Equations) :
    PairedWeylInput.action g (massMap c f) = massMap c ((spin c).dual g f) := by
  change PairedWeylInput.action g (zeroOdd c (raise f)) = _
  rw [zeroOdd_covariant,raise_covariant]
  rfl

def equationMap (kappa : ℂ) (mass yukawa : Bool → ℂ) (c : Bool) : Equations →ₗ[ℂ] A :=
  kappa • kineticMap c-mass c • massMap c-
    yukawa c • ((LocalPolynomial.leftMul phi.eval).comp (massMap c))

theorem equationMap_covariant (kappa : ℂ) (mass yukawa : Bool → ℂ)
    (c : Bool) (g : Group) (f : Equations) :
    PairedWeylInput.action g (equationMap kappa mass yukawa c f) =
      equationMap kappa mass yukawa c ((spin c).dual g f) := by
  simp only [equationMap,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.comp_apply,
    LocalPolynomial.leftMul,LinearMap.coe_mk,AddHom.coe_mk,map_sub,map_smul,kineticMap_covariant,massMap_covariant,
    action_mul,phi_invariant]

theorem equationMap_row (kappa : ℂ) (mass yukawa : Bool → ℂ) (c : Bool) (a : Fin 2) :
    equationMap kappa mass yukawa c (WeylLinearEquation.row a) =
      oddEquation kappa mass yukawa (c,a) := by
  have hm : massMap c (WeylLinearEquation.row a) = epsilon c a := raise_row c a
  simp only [equationMap,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.comp_apply,hm,
    LocalPolynomial.leftMul,LinearMap.coe_mk,AddHom.coe_mk,oddEquation]
  cases c <;> simp [kineticMap,seed,
    PairedWeylInput.left_row,PairedWeylInput.right_row]

theorem evenEquation_invariant (massSquared : ℂ) (yukawa : Bool → ℂ) (g : Group) :
    PairedWeylInput.action g (evenEquation massSquared yukawa) = evenEquation massSquared yukawa := by
  simp only [evenEquation,map_sub,map_neg,map_smul,wave_invariant,phi_invariant,pair_invariant]

theorem euler_span_stable (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ)
    (g : Group) (s : Field Label Label) :
    PairedWeylInput.action g ((density kappa massSquared mass yukawa).euler s) ∈
      Submodule.span ℂ (Set.range (density kappa massSquared mass yukawa).euler) := by
  let V := Submodule.span ℂ (Set.range (density kappa massSquared mass yukawa).euler)
  have hm (c : Bool) (a : Fin 2) :
      equationMap kappa mass yukawa c (WeylLinearEquation.row a) ∈ V := by
    rw [equationMap_row,← ScalarWeylYukawa.generated_odd kappa massSquared mass yukawa (c,a)]
    exact Submodule.subset_span ⟨_,rfl⟩
  have hf (c : Bool) (f : Equations) : equationMap kappa mass yukawa c f ∈ V :=
    TwoSidedCovariance.linear_two_mem _ V f _ _ _ _
      (PairedWeylInput.equation_expansion f) (hm c 0) (hm c 1)
  cases s with
  | inl j =>
    rw [ScalarWeylYukawa.generated_odd,← equationMap_row kappa mass yukawa j.1 j.2,equationMap_covariant]
    exact hf _ _
  | inr j =>
    rw [ScalarWeylYukawa.generated_even]
    split_ifs
    · rw [evenEquation_invariant]
      have he := ScalarWeylYukawa.generated_even kappa massSquared mass yukawa scalarLabel
      simp only [ite_true] at he
      rw [← he]
      exact Submodule.subset_span ⟨_,rfl⟩
    · rw [map_zero]; exact V.zero_mem

/-- The caller supplies parameters only; full EOM/IBP stability is derived. -/
def model (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) :
    LagrangianModel.Mixed Label Label (Fin 4) Group :=
  LagrangianModel.Mixed.ofEulerSpan (density kappa massSquared mass yukawa)
    PairedWeylInput.action action_mul
    (fun g i j => (LorentzDirections.direction g (Finsupp.single i 1)) j)
    PairedWeylInput.derivative_covariant (euler_span_stable kappa massSquared mass yukawa)

def input (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) :=
  (model kappa massSquared mass yukawa).input

def independentEuler (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) : Field Label Label → A
  | .inl j => oddEquation kappa mass yukawa j
  | .inr j => if j=scalarLabel then evenEquation massSquared yukawa else 0

theorem euler_equals_independent (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) :
    (density kappa massSquared mass yukawa).euler = independentEuler kappa massSquared mass yukawa := by
  funext s
  cases s with
  | inl j => exact ScalarWeylYukawa.generated_odd kappa massSquared mass yukawa j
  | inr j => exact ScalarWeylYukawa.generated_even kappa massSquared mass yukawa j

theorem full_relations (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) :
    (input kappa massSquared mass yukawa).relations = TwoSidedDifferential.combined D
      (Set.range (independentEuler kappa massSquared mass yukawa)) := by
  change (density kappa massSquared mass yukawa).relations = _
  unfold Expr.relations Expr.seeds
  rw [euler_equals_independent]

theorem coefficient_roundtrip (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ)
    (f : (input kappa massSquared mass yukawa).Coefficient) :
    (model kappa massSquared mass yukawa).equivalence.symm
      ((model kappa massSquared mass yukawa).equivalence f) = f :=
  (model kappa massSquared mass yukawa).equivalence.symm_apply_apply f

theorem odd_coefficient_equation (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ)
    (f : (input kappa massSquared mass yukawa).Coefficient) (j : Label) :
    f.val (oddEquation kappa mass yukawa j) = 0 := by
  rw [← ScalarWeylYukawa.generated_odd kappa massSquared mass yukawa j]
  exact f.property (TwoSidedDifferential.combined_seed _ _ ⟨_,rfl⟩)

theorem scalar_coefficient_equation (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ)
    (f : (input kappa massSquared mass yukawa).Coefficient) :
    f.val (evenEquation massSquared yukawa) = 0 := by
  have he := ScalarWeylYukawa.generated_even kappa massSquared mass yukawa scalarLabel
  simp only [ite_true] at he
  rw [← he]
  exact f.property (TwoSidedDifferential.combined_seed _ _ ⟨_,rfl⟩)

end
end Physics.YukawaModel
