import Math.RepresentationTheory.Constructions.PairedComponentFields
import Math.RepresentationTheory.Symmetric.SymmetricSquareContraction

/-! Canonical field/dual contractions in the actual polynomial jet algebra. -/
namespace Math.PairedJetContractions
set_option autoImplicit false
noncomputable section
open Representation PairedComponentFields
open scoped TensorProduct
variable {ι I H : Type*} [Fintype ι] [DecidableEq ι] [Group H]
abbrev A (ι I : Type*) := ScalarJetAlgebra.Algebra (Bool × ι) I
variable (rho : Representation ℂ H (V ι))

def action : Representation ℂ H (A ι I) :=
  JetFunctor.polynomialAction (JetLinear.action (I := I) (PairedComponentFields.action rho))
def transport (g : H) : A ι I →ₐ[ℂ] A ι I :=
  JetFunctor.polynomialMap (JetLinear.map (PairedComponentFields.action rho g))

def primal (a : I →₀ ℕ) : V ι →ₗ[ℂ] A ι I :=
  JetLinear.linearForm.comp ((JetLinear.atOrder a).comp
    (fieldEquiv.symm.toLinearMap.comp (LinearMap.inl ℂ (V ι) (Module.Dual ℂ (V ι)))))
def dual (a : I →₀ ℕ) : Module.Dual ℂ (V ι) →ₗ[ℂ] A ι I :=
  JetLinear.linearForm.comp ((JetLinear.atOrder a).comp
    (fieldEquiv.symm.toLinearMap.comp (LinearMap.inr ℂ (V ι) (Module.Dual ℂ (V ι)))))

theorem primal_covariant (g : H) (a : I →₀ ℕ) (v : V ι) :
    transport (I := I) rho g (primal a v) = primal a (rho g v) := by
  unfold primal
  simp only [LinearMap.comp_apply,LinearMap.inl_apply,LinearEquiv.coe_coe]
  change JetFunctor.polynomialMap _ (JetLinear.linearForm _) = _
  rw [JetFunctor.polynomialMap_linearForm,JetLinear.map_atOrder]
  apply congrArg (fun w => JetLinear.linearForm (JetLinear.atOrder a w))
  apply fieldEquiv.injective
  rw [fieldEquiv_action]
  simp

theorem dual_covariant (g : H) (a : I →₀ ℕ) (f : Module.Dual ℂ (V ι)) :
    transport (I := I) rho g (dual a f) = dual a (rho.dual g f) := by
  unfold dual
  simp only [LinearMap.comp_apply,LinearMap.inr_apply,LinearEquiv.coe_coe]
  change JetFunctor.polynomialMap _ (JetLinear.linearForm _) = _
  rw [JetFunctor.polynomialMap_linearForm,JetLinear.map_atOrder]
  apply congrArg (fun w => JetLinear.linearForm (JetLinear.atOrder a w))
  apply fieldEquiv.injective
  rw [fieldEquiv_action]
  simp

def contract (a b : I →₀ ℕ) :
    (V ι ⊗[ℂ] Module.Dual ℂ (V ι)) →ₗ[ℂ] A ι I := TensorProduct.lift {
  toFun v := {
    toFun f := primal a v*dual b f
    map_add' f h := by simp [map_add,mul_add]
    map_smul' c f := by simp [map_smul] }
  map_add' v w := by apply LinearMap.ext; intro f; simp [map_add,add_mul]
  map_smul' c v := by apply LinearMap.ext; intro f; simp [map_smul] }

theorem contract_covariant (g : H) (a b : I →₀ ℕ)
    (x : V ι ⊗[ℂ] Module.Dual ℂ (V ι)) :
    transport rho g (contract a b x) = contract a b ((rho.tprod rho.dual) g x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul v f =>
    change transport rho g (primal a v*dual b f) =
      primal a (rho g v)*dual b (rho.dual g f)
    rw [map_mul,primal_covariant,dual_covariant]

def canonical (a b : I →₀ ℕ) : A ι I :=
  contract a b (SymmetricSquareContraction.coevaluation (A := V ι))

theorem canonical_invariant (g : H) (a b : I →₀ ℕ) :
    transport rho g (canonical a b) = canonical a b := by
  rw [canonical,contract_covariant,
    SymmetricSquareContractionRepresentation.coevaluation_fixed]

theorem primal_basis (a : I →₀ ℕ) (i : ι) :
    primal a (Pi.single i 1) = MvPolynomial.X ((false,i),a) := by
  have he := congrArg fieldEquiv.symm (fieldEquiv_false i)
  simp only [LinearEquiv.symm_apply_apply] at he
  change JetLinear.linearForm (JetLinear.atOrder a (fieldEquiv.symm (Pi.single i 1,0))) = _
  rw [← he,JetLinear.atOrder_single]
  simp [JetLinear.linearForm]

theorem dual_basis (a : I →₀ ℕ) (i : ι) :
    dual a (dualCoordinates (Pi.single i 1)) = MvPolynomial.X ((true,i),a) := by
  have he := congrArg fieldEquiv.symm (fieldEquiv_true i)
  simp only [LinearEquiv.symm_apply_apply] at he
  change JetLinear.linearForm (JetLinear.atOrder a
    (fieldEquiv.symm (0,dualCoordinates (Pi.single i 1)))) = _
  rw [← he,JetLinear.atOrder_single]
  simp [JetLinear.linearForm]

theorem coevaluation_basis : SymmetricSquareContraction.coevaluation (A := V ι) =
    ∑ i, Pi.single i 1 ⊗ₜ[ℂ] dualCoordinates (Pi.single i 1) := by
  apply SymmetricSquareContraction.pairEnd.injective
  rw [SymmetricSquareContraction.coevaluation,LinearEquiv.apply_symm_apply,map_sum]
  apply LinearMap.ext
  intro x
  simp only [SymmetricSquareContraction.pairEnd_pure,LinearMap.sum_apply,
    LinearMap.smulRight_apply,PairedComponentFields.dual_basis,LinearMap.id_apply]
  ext i
  simp [Pi.single_apply]

theorem canonical_formula (a b : I →₀ ℕ) : canonical (ι := ι) a b =
    ∑ i, MvPolynomial.X ((false,i),a)*MvPolynomial.X ((true,i),b) := by
  rw [canonical,coevaluation_basis,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change primal a (Pi.single i 1)*dual b (dualCoordinates (Pi.single i 1)) = _
  rw [primal_basis,dual_basis]

end
end Math.PairedJetContractions
