import Math.RepresentationTheory.SymmetricInvariantPairing

/-! Symmetric evaluation coefficients with two possibly different quotients
of the repeated representation. No irreducibility or orthogonal splits needed. -/

namespace Math.PairwiseInvariantPairing
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection
open scoped TensorProduct

variable {H A B D R S : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup D] [Module ℂ D] [AddCommGroup R] [Module ℂ R]
  [AddCommGroup S] [Module ℂ S]
  {a : Representation ℂ H A} {b : Representation ℂ H B}
  {d : Representation ℂ H D} {r : Representation ℂ H R} {s : Representation ℂ H S}
  (ar : Split a r) (br : Split b r) (as' : Split a s) (ds : Split d s)

def coefficient : IntertwiningMap ((a.tprod a).tprod (b.dual.tprod d.dual))
    (Representation.trivial ℂ H ℂ) :=
  let f := (InvariantPairing.pulledCoefficient ar.project br.dual.project
    as'.project ds.dual.project).comp
      (OrderedInvariantPairing.swapMiddle a a b.dual d.dual).toIntertwiningMap
  f + f.comp (ExternalInvariantTensor.tensorEquiv
    (Representation.TensorProduct.comm a a)
    (Representation.Equiv.refl (b.dual.tprod d.dual))).toIntertwiningMap

@[simp] theorem apply_coefficient (x y : A) (u : Module.Dual ℂ B) (e : Module.Dual ℂ D) :
    coefficient ar br as' ds ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) =
      br.dual.project u (ar.project x) * ds.dual.project e (as'.project y) +
      br.dual.project u (ar.project y) * ds.dual.project e (as'.project x) := rfl

theorem swap (x y : A) (u : Module.Dual ℂ B) (e : Module.Dual ℂ D) :
    coefficient ar br as' ds ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) =
      coefficient ar br as' ds ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  simp only [apply_coefficient, add_comm]

theorem diagonal (x : A) (phi : Module.Dual ℂ R) (psi : Module.Dual ℂ S)
    (hphi : phi (ar.project x) = 1) (hpsi : psi (as'.project x) = 1) :
    coefficient ar br as' ds ((x ⊗ₜ[ℂ] x) ⊗ₜ[ℂ]
      (br.dual.embed phi ⊗ₜ[ℂ] ds.dual.embed psi)) = 2 := by
  simp only [apply_coefficient, br.dual.left_inv, ds.dual.left_inv, hphi, hpsi]
  norm_num

theorem exists_common_vector [Nontrivial R] [Nontrivial S] :
    ∃ x : A, ar.project x ≠ 0 ∧ as'.project x ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : R)
  obtain ⟨w, hw⟩ := exists_ne (0 : S)
  by_cases h1 : as'.project (ar.embed v) = 0
  · by_cases h2 : ar.project (as'.embed w) = 0
    · refine ⟨ar.embed v + as'.embed w, ?_, ?_⟩
      · simpa only [map_add, ar.left_inv, h2, add_zero] using hv
      · simpa only [map_add, as'.left_inv, h1, zero_add] using hw
    · exact ⟨as'.embed w, h2, by simpa only [as'.left_inv] using hw⟩
  · exact ⟨ar.embed v, by simpa only [ar.left_inv] using hv, h1⟩

theorem exists_diagonal [Nontrivial R] [Nontrivial S] :
    ∃ (x : A) (phi : Module.Dual ℂ R) (psi : Module.Dual ℂ S),
      phi (ar.project x) = 1 ∧ psi (as'.project x) = 1 := by
  obtain ⟨x, hr, hs⟩ := exists_common_vector ar as'
  obtain ⟨phi, hp⟩ := Module.Projective.exists_dual_eq_one ℂ hr
  obtain ⟨psi, hq⟩ := Module.Projective.exists_dual_eq_one ℂ hs
  exact ⟨x, phi, psi, hp, hq⟩

theorem coefficient_nonzero [Nontrivial R] [Nontrivial S] : coefficient ar br as' ds ≠ 0 := by
  obtain ⟨x, phi, psi, hp, hq⟩ := exists_diagonal ar as'
  intro hz
  have he := diagonal ar br as' ds x phi psi hp hq
  rw [hz] at he
  norm_num at he

theorem same_quotient (dr : Split d r) :
    coefficient ar br ar dr = SymmetricInvariantPairing.coefficient ar br dr := rfl

end
end Math.PairwiseInvariantPairing
