import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsSelection
import Math.Algebra.Jets.MixedFirstJetTensor

/-! Actual whole-grade first-derivative spinor tensors. A scalar extension
needs invariance only on the selected grade, never on the full jet algebra. -/
namespace Physics.WeylHiggsFirstTensor
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.MixedJetAlgebra PairedWeylKinetic WeylHiggsInput
open scoped TensorProduct
abbrev Spin := JetLinear.Field (Fin 2)
abbrev Dir := Math.MixedFirstJetTensor.Dir
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def oddField (c : Bool) : Spin →ₗ[ℂ] A :=
  (PairedWeylInput.oddInc c).comp (atOrder 0)

@[simp] theorem oddField_single (c : Bool) (a : Fin 2) (z : ℂ) :
    oddField c (Finsupp.single a z) = z • psi c a := by
  simp [oddField,PairedWeylInput.oddInc,PairedWeylInput.jetInc_single,
    JetFunctor.oddVector_single,psi]

theorem oddField_grade (c : Bool) (v : Spin) : oddField c v ∈ grade Label Label (Fin 4) 1 0 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
  | single a z => rw [oddField_single]; exact Submodule.smul_mem _ _ (WeylHiggsSelection.psi_grade c a)

def evenField (s : Label) : A := DerivativeLiteratureMixed.h s.1 s.2
def rest (b : Fin 4 → Label) : A := evenField (b 1)*evenField (b 2)*evenField (b 3)
def word (c d : Bool) (b : Fin 4 → Label) (r : Fin 3) (u : Dir) (x y : Spin) : A :=
  Math.MixedFirstJetTensor.word D (oddField c) (oddField d) (evenField (b 0)) (rest b) r u x y
def tensor (f : A →ₗ[ℂ] ℂ) (c d : Bool) (b : Fin 4 → Label) (r : Fin 3) :=
  Math.MixedFirstJetTensor.tensor D (oddField c) (oddField d) (evenField (b 0)) (rest b) f r

theorem tensor_apply (f : A →ₗ[ℂ] ℂ) (c d : Bool) (b : Fin 4 → Label)
    (r : Fin 3) (u : Dir) (x y : Spin) : tensor f c d b r x y u = f (word c d b r u x y) := rfl

theorem directional_grade (u : Dir) {n m e : ℕ} {p : A}
    (hp : p ∈ grade Label Label (Fin 4) n m e) :
    Math.MixedFirstJetTensor.directional D u p ∈ grade Label Label (Fin 4) n m (e+1) := by
  rw [Math.MixedFirstJetTensor.directional_apply]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (totalDerivative_mem i hp))

theorem word_grade (c d : Bool) (b : Fin 4 → Label) (r : Fin 3) (u : Dir) (x y : Spin) :
    word c d b r u x y ∈ V := by
  have he (s : Label) : evenField s ∈ grade Label Label (Fin 4) 0 1 0 :=
    WeylHiggsSelection.h_grade s.1 s.2
  have hr : rest b ∈ grade Label Label (Fin 4) 0 3 0 :=
    mul_mem (F := Label) (B := Label)
      (mul_mem (F := Label) (B := Label) (he (b 1)) (he (b 2))) (he (b 3))
  exact Math.MixedFirstJetTensor.mixed_word_mem (F := Label) (B := Label) (oddField c) (oddField d)
    (evenField (b 0)) (rest b) (oddField_grade c) (oddField_grade d) (he (b 0)) hr r u x y

def transport (g : Group) : A →ₐ[ℂ] A :=
  Algebra.TensorProduct.map (ExteriorAlgebra.map (jets g)) (JetFunctor.polynomialMap (bosons g))
theorem transport_apply (g : Group) (p : A) : transport g p = action g p := rfl

theorem odd_lorentz (c : Bool) (g : LorentzDirections.Group) (x : Spin) :
    transport (1,g) (oddField c x) = oddField c (LorentzJetIBP.weyl c g x) := by
  change action (1,g) (PairedWeylInput.oddInc c (atOrder 0 x)) = _
  rw [WeylHiggsInput.oddInc_covariant,Math.JetDirections.combined_zero]
  simp [StandardSMGaugeTensor.phase,oddField]

theorem even_lorentz (g : LorentzDirections.Group) (s : Label) :
    transport (1,g) (evenField s) = evenField s := by
  have he : evenField s = scalarEmbed (DerivativeLiteratureHiggs.h s.1 s.2) := rfl
  rw [he]
  change JetFunctor.mixedAction jets bosons (1,g) (MixedScalarInclusion.embed _) = _
  rw [MixedScalarInclusion.natural]
  change scalarEmbed (HiggsStandardInput.transport (1,g) _) = _
  rw [HiggsStandardInput.factorize,HiggsLagrangianInput.field_invariant]
  simp only [HiggsInternalSymmetry.transport,PairedJetContractions.transport,map_one]
  change scalarEmbed (JetFunctor.polynomialMap (JetLinear.map
    (LinearMap.id : JetLinear.Field Label →ₗ[ℂ] JetLinear.Field Label)) _) = _
  rw [JetLinear.map_id,JetFunctor.polynomialMap_id]
  rfl

theorem rest_lorentz (g : LorentzDirections.Group) (b : Fin 4 → Label) :
    transport (1,g) (rest b) = rest b := by
  simp only [rest,map_mul,even_lorentz]

theorem directional_covariant (g : Group) (u : Dir) (p : A) :
    transport g (Math.MixedFirstJetTensor.directional D u p) =
      Math.MixedFirstJetTensor.directional D (directions g u) (transport g p) :=
  Math.MixedFirstJetTensor.directional_covariant D (transport g).toLinearMap (directions g)
    (derivative_covariant g) u p

theorem word_lorentz (g : LorentzDirections.Group) (c d : Bool) (b : Fin 4 → Label)
    (r : Fin 3) (u : Dir) (x y : Spin) :
    transport (1,g) (word c d b r u x y) =
      word c d b r (LorentzDirections.direction g u)
        (LorentzJetIBP.weyl c g x) (LorentzJetIBP.weyl d g y) :=
  Math.MixedFirstJetTensor.transport_word D (oddField c) (oddField d)
    (evenField (b 0)) (rest b) (transport (1,g))
    (LorentzJetIBP.weyl c g) (LorentzJetIBP.weyl d g) (LorentzDirections.direction g)
    (odd_lorentz c g) (odd_lorentz d g) (even_lorentz g (b 0))
    (rest_lorentz g b) (directional_covariant (1,g)) r u x y

theorem tensor_invariant (f : A →ₗ[ℂ] ℂ)
    (h : ∀ g p, p ∈ V → f (action g p) = f p)
    (c d : Bool) (b : Fin 4 → Label) (r : Fin 3)
    (g : LorentzDirections.Group) (x y : Spin) (u : Dir) :
    tensor f c d b r (LorentzJetIBP.weyl c g x) (LorentzJetIBP.weyl d g y)
      (LorentzDirections.direction g u) = tensor f c d b r x y u := by
  change f (word c d b r _ _ _) = f (word c d b r u x y)
  rw [← word_lorentz,transport_apply]
  exact h (1,g) _ (word_grade c d b r u x y)

end
end Physics.WeylHiggsFirstTensor
