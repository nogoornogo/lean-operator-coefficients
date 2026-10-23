import Physics.FieldTheory.Jets.Weyl.Equations.PairedWeylGeneratedInput

/-! The ordered Pauli current is a vector-valued source, dual to the
ordinary jet directions. The statement uses the actual paired Weyl action. -/
namespace Physics.WeylCurrentCovariance
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections
open PairedWeylKinetic
open scoped TensorProduct

@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def component (c : Bool) (g : LorentzDirections.Group) (b a : Fin 2) : ℂ :=
  if c then star ((g : LorentzDirections.Mat) b a) else (g : LorentzDirections.Mat) b a

theorem field_components (c : Bool) (g : LorentzDirections.Group) (a : Fin 2) :
    LorentzJetIBP.weyl c g (Finsupp.single a 1) =
      ∑ b : Fin 2, component c g b a • Finsupp.single b 1 := by
  apply LorentzJetIBP.spinorBasis.injective
  rw [LorentzJetIBP.weyl_basis]
  ext b
  cases c <;> fin_cases b <;> simp [component, LorentzJetIBP.spinorBasis,
    WeylSpinor.left, WeylSpinor.right, WeylSpinor.conjugate,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem psi_covariant (c : Bool) (g : LorentzDirections.Group) (a : Fin 2) :
    PairedWeylInput.action g (psi c a) = ∑ b : Fin 2, component c g b a • psi c b := by
  have h (b : Fin 2) : PairedWeylInput.oddInc c (atOrder (I := Fin 4) 0
      (Finsupp.single b 1)) = psi c b := by
    simp [atOrder, PairedWeylInput.oddInc, PairedWeylInput.jetInc_single,
      JetFunctor.oddVector_single, psi]
  rw [← h a, PairedWeylInput.oddInc_covariant, combined_zero, field_components,
    map_sum, map_sum]
  simp only [map_smul, h]

def matrixCurrent : LorentzDirections.Mat →ₗ[ℂ] A where
  toFun m := ∑ a : Fin 2, ∑ b : Fin 2, m a b • (psi false a * psi true b)
  map_add' m n := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z m := by simp [mul_smul]

theorem matrix_covariant (g : LorentzDirections.Group) (m : LorentzDirections.Mat) :
    PairedWeylInput.action g (matrixCurrent m) =
      matrixCurrent (LorentzDirections.matrixAction g m) := by
  change PairedWeylInput.action g
    (∑ a : Fin 2, ∑ b : Fin 2, m a b • (psi false a * psi true b)) =
    ∑ a : Fin 2, ∑ b : Fin 2,
      (LorentzDirections.matrixAction g m) a b • (psi false a * psi true b)
  simp only [map_sum, map_smul]
  simp_rw [show ∀ x y : A, PairedWeylInput.action g (x*y) =
      PairedWeylInput.action g x * PairedWeylInput.action g y from
    JetFunctor.mixedAction_mul _ _ g, psi_covariant]
  simp only [Fin.sum_univ_two, component, Bool.false_eq_true, ite_false, ite_true,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    LorentzDirections.matrixAction_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  module

def vectorCurrent : LorentzDirections.Coordinates →ₗ[ℂ] A :=
  matrixCurrent.comp LorentzDirections.pauli

theorem vector_covariant (g : LorentzDirections.Group) (v : LorentzDirections.Coordinates) :
    PairedWeylInput.action g (vectorCurrent v) =
      vectorCurrent (LorentzDirections.vector g v) := by
  change PairedWeylInput.action g (matrixCurrent (LorentzDirections.pauli v)) = _
  rw [matrix_covariant, LorentzDirections.matrixAction_apply, ← LorentzDirections.pauli_vector]
  rfl

theorem current_dictionary (i : Fin 4) :
    DerivativeLiteratureMixed.current i = vectorCurrent (Pi.single i 1) := rfl

theorem current_covariant (g : LorentzDirections.Group) (i : Fin 4) :
    PairedWeylInput.action g (DerivativeLiteratureMixed.current i) =
      ∑ j : Fin 4, (LorentzDirections.vector g (Pi.single i 1)) j •
        DerivativeLiteratureMixed.current j := by
  rw [current_dictionary, vector_covariant]
  conv_lhs => rw [WeylLinearEquation.expand (LorentzDirections.vector g (Pi.single i 1))]
  rw [map_sum]
  simp only [map_smul, ← current_dictionary]

end
end Physics.WeylCurrentCovariance
