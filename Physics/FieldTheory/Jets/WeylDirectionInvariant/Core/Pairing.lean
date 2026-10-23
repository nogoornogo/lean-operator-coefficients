import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.Basic

/-! The inverse-Pauli spinor/dual-vector contraction is invariant under
arbitrary actual SL(2,C) elements, independently of the finite upper rows. -/
namespace Physics.WeylDirectionInvariant
set_option autoImplicit false
noncomputable section
open Math Matrix LorentzDirections LorentzFiniteControls

def pair (u : Dir) (v : Coordinates) : ℂ := ∑ i : Fin 4, u i * v i

theorem pair_dual (u : Dir) (v : Coordinates) : pair u v = dualEquiv.symm u v := by
  induction u using Finsupp.induction_linear with
  | zero => simp [pair]
  | add u w hu hw => simp [pair,Finsupp.add_apply,add_mul,Finset.sum_add_distrib,← hu,← hw]
  | single i c =>
    have he : dualEquiv.symm (Finsupp.single i 1) = (Pi.basisFun ℂ (Fin 4)).dualBasis i :=
      (LinearEquiv.symm_apply_eq _).mpr (Module.Basis.repr_self _ _).symm
    rw [show Finsupp.single i c = c • Finsupp.single i (1 : ℂ) by simp,map_smul,he]
    simp [pair,Finsupp.single_apply]

theorem pair_invariant (g : Group) (u : Dir) (v : Coordinates) :
    pair (direction g u) (vector g v) = pair u v := by
  rw [pair_dual,pair_dual]
  change (dualEquiv.symm (dualEquiv (vector.dual g (dualEquiv.symm u)))) (vector g v) = _
  rw [dualEquiv.symm_apply_apply]
  change (dualEquiv.symm u) (vector g⁻¹ (vector g v)) = _
  rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one]
  rfl

def spinVector (x y : Spin) : Coordinates :=
  fromPauli (outer (LorentzJetIBP.spinorBasis x) (LorentzJetIBP.spinorBasis y))

theorem pauli_from (m : Mat) : pauli (fromPauli m) = m := pauliEquiv.apply_symm_apply m

theorem spinVector_covariant (g : Group) (x y : Spin) :
    spinVector (LorentzJetIBP.weyl false g x) (LorentzJetIBP.weyl true g y) =
      vector g (spinVector x y) := by
  unfold spinVector
  rw [LorentzJetIBP.weyl_basis,LorentzJetIBP.weyl_basis]
  change fromPauli (outer (WeylSpinor.left g _) (WeylSpinor.right g _)) =
    fromPauli ((g : Mat)*pauli (fromPauli (outer _ _))*(g : Mat)ᴴ)
  rw [pauli_from]
  exact congrArg fromPauli (left_right_matrix g _ _).symm

def contraction (x y : Spin) (u : Dir) : ℂ := pair u (spinVector x y)

theorem contraction_invariant (g : Group) (x y : Spin) (u : Dir) :
    contraction (LorentzJetIBP.weyl false g x) (LorentzJetIBP.weyl true g y) (direction g u) =
      contraction x y u := by
  simp only [contraction,spinVector_covariant,pair_invariant]

theorem contraction_basis (a b : Fin 2) (i : Fin 4) :
    contraction (S a) (S b) (E i) = kernel a b i / 2 := by
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    norm_num [contraction,pair,spinVector,kernel,fromPauli,outer,
      LorentzJetIBP.spinorBasis,S,E,Finsupp.single_apply,Fin.sum_univ_succ]

end
end Physics.WeylDirectionInvariant
