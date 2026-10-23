import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.Pairing

/-! Component certificates for the inverse-Pauli contraction imply actual
full-group invariance of curried spinor/dual-vector tensors. -/
namespace Physics.WeylDirectionInvariant
set_option autoImplicit false
noncomputable section
open Math LorentzDirections LorentzFiniteControls

theorem tensor_ext {f g : Tensor} (h : ∀ a b i, component f a b i = component g a b i) : f = g := by
  apply (Finsupp.basisSingleOne : Module.Basis (Fin 2) ℂ Spin).ext
  intro a
  apply (Finsupp.basisSingleOne : Module.Basis (Fin 2) ℂ Spin).ext
  intro b
  apply (Finsupp.basisSingleOne : Module.Basis (Fin 4) ℂ Dir).ext
  intro i
  exact h a b i

theorem spinVector_add_left (x y z : Spin) : spinVector (x+y) z = spinVector x z+spinVector y z := by
  have he : outer (LorentzJetIBP.spinorBasis (x+y)) (LorentzJetIBP.spinorBasis z) =
      outer (LorentzJetIBP.spinorBasis x) (LorentzJetIBP.spinorBasis z)+
        outer (LorentzJetIBP.spinorBasis y) (LorentzJetIBP.spinorBasis z) := by
    ext a b
    simp [outer,add_mul]
  unfold spinVector
  rw [he,map_add]

theorem spinVector_add_right (x y z : Spin) : spinVector x (y+z) = spinVector x y+spinVector x z := by
  have he : outer (LorentzJetIBP.spinorBasis x) (LorentzJetIBP.spinorBasis (y+z)) =
      outer (LorentzJetIBP.spinorBasis x) (LorentzJetIBP.spinorBasis y)+
        outer (LorentzJetIBP.spinorBasis x) (LorentzJetIBP.spinorBasis z) := by
    ext a b
    simp [outer,mul_add]
  unfold spinVector
  rw [he,map_add]

theorem spinVector_smul_left (c : ℂ) (x y : Spin) : spinVector (c • x) y = c • spinVector x y := by
  have he : outer (LorentzJetIBP.spinorBasis (c • x)) (LorentzJetIBP.spinorBasis y) =
      c • outer (LorentzJetIBP.spinorBasis x) (LorentzJetIBP.spinorBasis y) := by
    ext a b
    simp [outer,mul_assoc]
  unfold spinVector
  rw [he,map_smul]

theorem spinVector_smul_right (c : ℂ) (x y : Spin) : spinVector x (c • y) = c • spinVector x y := by
  have he : outer (LorentzJetIBP.spinorBasis x) (LorentzJetIBP.spinorBasis (c • y)) =
      c • outer (LorentzJetIBP.spinorBasis x) (LorentzJetIBP.spinorBasis y) := by
    ext a b
    simp [outer,mul_left_comm]
  unfold spinVector
  rw [he,map_smul]

def canonical1 (x y : Spin) : Dir →ₗ[ℂ] ℂ where
  toFun u := contraction x y u
  map_add' u v := by simp [contraction,pair,Finsupp.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' c u := by simp [contraction,pair,Finsupp.smul_apply,Finset.mul_sum,mul_assoc]

def canonical2 (x : Spin) : Spin →ₗ[ℂ] Dir →ₗ[ℂ] ℂ where
  toFun y := canonical1 x y
  map_add' y z := by
    ext u
    simp [canonical1,contraction,spinVector_add_right,pair,mul_add,Finset.sum_add_distrib]
  map_smul' c y := by
    ext u
    simp [canonical1,contraction,spinVector_smul_right,pair,Finset.mul_sum,mul_left_comm]

def canonical : Tensor where
  toFun x := canonical2 x
  map_add' x y := by
    ext z u
    simp [canonical2,canonical1,contraction,spinVector_add_left,pair,mul_add,Finset.sum_add_distrib]
  map_smul' c x := by
    ext y u
    simp [canonical2,canonical1,contraction,spinVector_smul_left,pair,Finset.mul_sum,mul_left_comm]

theorem canonical_apply (x y : Spin) (u : Dir) : canonical x y u = contraction x y u := rfl

theorem invariant_of_components (f : Tensor) (scale : ℂ)
    (h : ∀ a b i, component f a b i = scale*contraction (S a) (S b) (E i))
    (g : Group) (x y : Spin) (u : Dir) :
    f (LorentzJetIBP.weyl false g x) (LorentzJetIBP.weyl true g y) (direction g u) = f x y u := by
  have he : f = scale • canonical := by
    apply tensor_ext
    intro a b i
    simpa only [component,LinearMap.smul_apply,smul_eq_mul,canonical_apply] using h a b i
  rw [he]
  simp only [LinearMap.smul_apply,canonical_apply,smul_eq_mul,contraction_invariant]

theorem invariant_of_transposed_components (f : Tensor) (scale : ℂ)
    (h : ∀ a b i, component f a b i = scale*contraction (S b) (S a) (E i))
    (g : Group) (x y : Spin) (u : Dir) :
    f (LorentzJetIBP.weyl true g x) (LorentzJetIBP.weyl false g y) (direction g u) = f x y u := by
  have hf : ∀ a b i, component f.flip a b i = scale*contraction (S a) (S b) (E i) := by
    intro a b i
    exact h b a i
  exact invariant_of_components f.flip scale hf g y x u

end
end Physics.WeylDirectionInvariant
