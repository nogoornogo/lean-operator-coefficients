import Physics.FieldTheory.Jets.Lagrangian.YukawaModel
import Math.RepresentationTheory.Jets.PairedJetContractions

/-! Independent invariance of the total density. The model's Euler covariance
was proved separately, so these checks do not assume a variational naturality
theorem that the current expression compiler does not supply. -/
namespace Physics.YukawaModel
set_option autoImplicit false
noncomputable section
open Math Math.LocalPolynomial.Expr Math.ScalarWeylYukawa Math.PairedWeylKinetic
open Math.JetLinear Math.JetDirections
open scoped TensorProduct
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def kineticContraction (c : Bool) : Spinor ⊗[ℂ] Equations →ₗ[ℂ] A := TensorProduct.lift {
  toFun v := {
    toFun f := zeroOdd c v*kineticMap c f
    map_add' f h := by simp only [map_add,mul_add]
    map_smul' z f := by simp only [map_smul,mul_smul_comm,RingHom.id_apply] }
  map_add' v w := by ext f; simp only [map_add,add_mul,LinearMap.add_apply,LinearMap.coe_mk,AddHom.coe_mk]
  map_smul' z v := by ext f; simp only [map_smul,smul_mul_assoc,LinearMap.smul_apply,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] }

theorem kineticContraction_covariant (c : Bool) (g : Group) (x : Spinor ⊗[ℂ] Equations) :
    PairedWeylInput.action g (kineticContraction c x) =
      kineticContraction c (((spin c).tprod (spin c).dual) g x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul v f =>
    change PairedWeylInput.action g (zeroOdd c v*kineticMap c f) =
      zeroOdd c (spin c g v)*kineticMap c ((spin c).dual g f)
    rw [action_mul,zeroOdd_covariant,kineticMap_covariant]

theorem kineticTerm_eval (a b : Fin 2) (i : Fin 4) :
    (term a b i).eval = psi true a*D i (psi false b) := by
  change (Math.LocalPolynomial.Expr.fermion (true,a)).eval *
    (Math.LocalPolynomial.Expr.jet (.inl (false,b)) [i]).eval = _
  rw [eval_jet_word]
  rfl

theorem kinetic_expansion : PairedWeylKinetic.density.eval =
    kineticContraction true (SymmetricSquareContraction.coevaluation (A := Spinor)) := by
  have hf (a : Fin 2) : PairedComponentFields.dualCoordinates (Pi.single a 1) =
      WeylLinearEquation.row a := by
    apply LinearMap.ext
    intro v
    exact PairedComponentFields.dual_basis a v
  rw [PairedJetContractions.coevaluation_basis,map_sum]
  simp only [Fin.sum_univ_two]
  change PairedWeylKinetic.density.eval =
    zeroOdd true (Pi.single 0 1)*kineticMap true (PairedComponentFields.dualCoordinates (Pi.single 0 1))+
    zeroOdd true (Pi.single 1 1)*kineticMap true (PairedComponentFields.dualCoordinates (Pi.single 1 1))
  rw [hf,hf,zeroOdd_basis,zeroOdd_basis]
  simp only [kineticMap,ite_true,PairedWeylInput.left_row]
  simp only [PairedWeylKinetic.density,eval_add,eval_sub,eval_smul,kineticTerm_eval,
    left,ite_true]
  norm_num only [show (1:Fin 2) ≠ 0 from by decide,ite_false]
  simp only [mul_add,mul_sub,mul_smul_comm]
  abel

theorem fermion_kinetic_invariant (g : Group) :
    PairedWeylInput.action g PairedWeylKinetic.density.eval = PairedWeylKinetic.density.eval := by
  rw [kinetic_expansion,kineticContraction_covariant,
    SymmetricSquareContractionRepresentation.coevaluation_fixed]

def scalarFieldInclusion : JetLinear.Field Unit →ₗ[ℂ] JetLinear.Field Label :=
  Finsupp.linearCombination ℂ (fun _ => Finsupp.single scalarLabel (1:ℂ))

def scalarInclusion : ScalarJetAlgebra.Algebra Unit (Fin 4) →ₐ[ℂ]
    ScalarJetAlgebra.Algebra Label (Fin 4) :=
  JetFunctor.polynomialMap (JetLinear.map scalarFieldInclusion)

theorem scalarInclusion_X (j : ScalarJetAlgebra.Index Unit (Fin 4)) :
    scalarInclusion (MvPolynomial.X j) = MvPolynomial.X (scalarLabel,j.2) := by
  obtain ⟨u,a⟩ := j
  cases u
  simp [scalarInclusion,JetFunctor.polynomialMap_X,JetLinear.map_single,
    scalarFieldInclusion,JetLinear.linearForm]

theorem scalarInclusion_natural (g : Group) (p : ScalarJetAlgebra.Algebra Unit (Fin 4)) :
    HiggsLagrangianInput.transport g (scalarInclusion p) =
      scalarInclusion (LorentzJetIBP.scalarAction g p) := by
  have he : (jetMap (S := Label) (LorentzDirections.direction g)).comp (JetLinear.map scalarFieldInclusion) =
      (JetLinear.map scalarFieldInclusion).comp (jetMap (S := Unit) (LorentzDirections.direction g)) :=
    LinearMap.ext (internal_commute scalarFieldInclusion (LorentzDirections.direction g))
  change JetFunctor.polynomialMap _ (JetFunctor.polynomialMap _ p) =
    JetFunctor.polynomialMap _ (JetFunctor.polynomialMap (combined _ _ g) p)
  rw [show combined LorentzJetIBP.scalarField LorentzDirections.direction g =
      jetMap (S := Unit) (LorentzDirections.direction g) from combined_trivial _ _]
  rw [← AlgHom.comp_apply,← JetFunctor.polynomialMap_comp,he,JetFunctor.polynomialMap_comp]
  rfl

theorem scalar_kinetic_expansion : scalarKinetic.eval =
    (1/2:ℂ) • MixedScalarInclusion.embed (scalarInclusion LorentzJetIBP.kinetic) := by
  rw [LorentzJetIBP.kinetic_formula]
  simp only [map_sub,map_pow,scalarInclusion_X,scalarKinetic,directionalKinetic,
    eval_sub,eval_smul,eval_pow,eval_derivative]
  simp only [phi,boson,Math.LocalPolynomial.Expr.eval,wordIndex,
    MixedJetAlgebra.totalDerivative_even,ScalarJetAlgebra.shift,zero_add,smul_sub]
  rfl

theorem scalar_kinetic_invariant (g : Group) :
    PairedWeylInput.action g scalarKinetic.eval = scalarKinetic.eval := by
  rw [scalar_kinetic_expansion,map_smul,even_transport,scalarInclusion_natural,
    LorentzJetIBP.kinetic_invariant]

theorem density_invariant (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) (g : Group) :
    PairedWeylInput.action g (density kappa massSquared mass yukawa).eval =
      (density kappa massSquared mass yukawa).eval := by
  simp only [ScalarWeylYukawa.density,eval_sub,eval_add,eval_smul,eval_pow,eval_mul,map_sub,map_add,map_smul,
    scalar_kinetic_invariant,fermion_kinetic_invariant,pow_two,action_mul,phi_invariant,pair_invariant]

end
end Physics.YukawaModel
