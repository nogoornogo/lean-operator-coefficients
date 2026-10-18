import GUT.PatiSalam.Embeddings.PhiRepresentation

/-! Internal gauge action comparison; spin/statistics are separate interfaces. -/
namespace GUT.PatiSalam.InvariantAction
set_option autoImplicit false
noncomputable section
open StandardModelEmbedding ComponentRepresentations
open scoped TensorProduct Matrix

def hermitian {n : Type*} [Fintype n] (v w : n → ℂ) : ℂ := star v ⬝ᵥ w

theorem hermitian_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (g : Matrix.unitaryGroup n ℂ) (v w : n → ℂ) :
    hermitian (g.val.mulVec v) (g.val.mulVec w) = hermitian v w := by
  have hg : g.val.conjTranspose * g.val = 1 := Matrix.UnitaryGroup.star_mul_self g
  rw [hermitian,Matrix.star_mulVec,← Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,hg]
  simp [hermitian]

theorem contraction_tmul (v w : Four) (x y : Two) :
    ComponentAdmission.contraction (arrayEquiv (v ⊗ₜ[ℂ] x)) (arrayEquiv (w ⊗ₜ[ℂ] y)) =
      hermitian v w * hermitian x y := by
  simp [ComponentAdmission.contraction,hermitian,dotProduct,Finset.sum_mul,
    star_mul,mul_mul_mul_comm]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem contraction_add_left (a b c : ComponentAdmission.Array) :
    ComponentAdmission.contraction (a+b) c = ComponentAdmission.contraction a c +
      ComponentAdmission.contraction b c := by
  simp [ComponentAdmission.contraction,add_mul,Finset.sum_add_distrib]
theorem contraction_add_right (a b c : ComponentAdmission.Array) :
    ComponentAdmission.contraction a (b+c) = ComponentAdmission.contraction a b +
      ComponentAdmission.contraction a c := by
  simp [ComponentAdmission.contraction,mul_add,Finset.sum_add_distrib]

theorem contraction_invariant (rho : Representation ℂ PSGroup Two)
    (hrho : ∀ g, ∃ u : Matrix.unitaryGroup (Fin 2) ℂ, rho g = Matrix.toLin' u.val)
    (g : PSGroup) (a b : Multiplet) :
    ComponentAdmission.contraction (arrayEquiv ((four.tprod rho) g a))
      (arrayEquiv ((four.tprod rho) g b)) =
      ComponentAdmission.contraction (arrayEquiv a) (arrayEquiv b) := by
  induction a using TensorProduct.inductionOn with
  | tmul v x =>
      induction b using TensorProduct.inductionOn with
      | tmul w y =>
          obtain ⟨u,hu⟩ := hrho g
          simp only [Representation.tprod_apply,TensorProduct.map_tmul,contraction_tmul]
          rw [hu]
          change hermitian ((g.1.val).mulVec v) ((g.1.val).mulVec w) *
            hermitian (u.val.mulVec x) (u.val.mulVec y) = _
          rw [hermitian_unitary ⟨g.1.val,Matrix.specialUnitaryGroup_le_unitaryGroup g.1.prop⟩,
            hermitian_unitary u]
      | add b c hb hc => simp only [map_add,contraction_add_right,hb,hc]
  | add a c ha hc => simp only [map_add,contraction_add_left,ha,hc]

theorem chi_invariant (g : PSGroup) (a b : Multiplet) :
    ComponentAdmission.contraction (arrayEquiv (fR g a)) (arrayEquiv (fR g b)) =
      ComponentAdmission.contraction (arrayEquiv a) (arrayEquiv b) := by
  apply contraction_invariant right
  intro h
  exact ⟨⟨h.2.2.val,Matrix.specialUnitaryGroup_le_unitaryGroup h.2.2.prop⟩,rfl⟩

def phiOperator (phi : PhiRepresentation.Phi) : Multiplet →ₗ[ℂ] Multiplet :=
  TensorProduct.map LinearMap.id phi

theorem phi_covariant (g : PSGroup) (phi : PhiRepresentation.Phi) (v : Multiplet) :
    phiOperator (PhiRepresentation.representation g phi) (fR g v) =
      fL g (phiOperator phi v) := by
  induction v using TensorProduct.inductionOn with
  | tmul a x =>
      simp only [phiOperator,fR,fL,Representation.tprod_apply,TensorProduct.map_tmul,
        LinearMap.id_apply,PhiRepresentation.representation,Representation.linHom_apply,
        LinearMap.comp_apply]
      have hx : right g⁻¹ (right g x) = x := by
        rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one]
        rfl
      rw [hx]
  | add v w hv hw => simp only [map_add,hv,hw]

def phiYukawa (l : Multiplet) (phi : PhiRepresentation.Phi) (r : Multiplet) : ℂ :=
  ComponentAdmission.contraction (arrayEquiv l) (arrayEquiv (phiOperator phi r))

theorem phiYukawa_invariant (g : PSGroup) (l r : Multiplet) (phi : PhiRepresentation.Phi) :
    phiYukawa (fL g l) (PhiRepresentation.representation g phi) (fR g r) =
      phiYukawa l phi r := by
  rw [phiYukawa,phi_covariant]
  apply contraction_invariant left
  intro h
  exact ⟨⟨h.2.1.val,Matrix.specialUnitaryGroup_le_unitaryGroup h.2.1.prop⟩,rfl⟩

theorem phi_array (m : Matrix (Fin 2) (Fin 2) ℂ) (v : Multiplet) (a : Fin 4) (i : Fin 2) :
    arrayEquiv (phiOperator (Matrix.toLin' m) v) a i =
      ∑ j, m i j * arrayEquiv v a j := by
  induction v using TensorProduct.inductionOn with
  | tmul c w =>
      simp [phiOperator,Matrix.toLin'_apply,Matrix.mulVec,dotProduct]
      ring
  | add v w hv hw => simp [hv,hw,mul_add,Finset.sum_add_distrib]

theorem phiYukawa_array (l r : Multiplet) (m : Matrix (Fin 2) (Fin 2) ℂ) :
    phiYukawa l (Matrix.toLin' m) r =
      ∑ a, ∑ i, ∑ j, star (arrayEquiv l a i) * m i j * arrayEquiv r a j := by
  simp [phiYukawa,ComponentAdmission.contraction,phi_array,mul_add,mul_assoc]

theorem chi_array_invariant (g : PSGroup) (a b : ComponentAdmission.Array) :
    ComponentAdmission.contraction (chiRepresentation g a) (chiRepresentation g b) =
      ComponentAdmission.contraction a b := by
  have h := chi_invariant g (arrayEquiv.symm a) (arrayEquiv.symm b)
  change ComponentAdmission.contraction (arrayEquiv (fR g (arrayEquiv.symm a)))
    (arrayEquiv (fR g (arrayEquiv.symm b))) = _
  simpa only [LinearEquiv.apply_symm_apply] using h

end
end GUT.PatiSalam.InvariantAction
