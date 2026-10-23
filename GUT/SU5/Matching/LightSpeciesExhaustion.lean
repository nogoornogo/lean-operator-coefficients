import GUT.SU5.Matching.LightSpeciesMaps

open Physics

open Math

/-! Every vector in the canonical full-species images is a sum of the
explicit generation embeddings, not merely a chosen constituent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU5.LightSpeciesExhaustion
noncomputable section
open Representation MatterSource GeorgiGlashowSource LightRadical LightSpeciesMaps
open ProductFactorization StandardSMGaugeTensor SMEpsilonTensor
open scoped TensorProduct
variable {H : Type*} [Group H] {n : ℕ} (R : OrdinaryAction H n)

theorem read_insert_cross (a b : Fin n) (x : Matter.Ten) :
    readTen a (insertTen b x) = if a = b then x else 0 := by
  classical
  by_cases h : a = b
  · subst b; simp [read_insert]
  · simp [readTen, insertTen, gatherGenerations, h]

def readQ (a : Fin n) : Light R →ₗ[ℂ] Quark :=
  (LinearMap.fst ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp
    (ExteriorSquareBranching.branch.comp (readSM R a).toLinearMap))

def insertUp (a : Fin n) : Module.Dual ℂ Color →ₗ[ℂ] Light R :=
  (insertSM R a).toLinearMap.comp (ExteriorSquareBranching.tenEquiv.symm.toLinearMap.comp
    (LinearMap.inl ℂ _ _))

def insertElectron (a : Fin n) : Module.Dual ℂ ℂ →ₗ[ℂ] Light R :=
  (insertSM R a).toLinearMap.comp (ExteriorSquareBranching.tenEquiv.symm.toLinearMap.comp
    ((LinearMap.inr ℂ _ _).comp (LinearMap.inr ℂ _ _)))

def readU (a : Fin n) : Module.Dual ℂ (Light R) →ₗ[ℂ] Color :=
  (Module.evalEquiv ℂ Color).symm.toLinearMap.comp (insertUp R a).dualMap

def readE (a : Fin n) : Module.Dual ℂ (Light R) →ₗ[ℂ] ℂ :=
  (Module.evalEquiv ℂ ℂ).symm.toLinearMap.comp (insertElectron R a).dualMap

private theorem branch_symm (x : ExteriorSquareBranching.Blocks) :
    ExteriorSquareBranching.branch (ExteriorSquareBranching.tenEquiv.symm x) = x :=
  ExteriorSquareBranching.tenEquiv.apply_symm_apply x

theorem readQ_embed (a b : Fin n) (q : Quark) :
    readQ R a (LightRadical.quark R b q) = if a = b then q else 0 := by
  classical
  change (ExteriorSquareBranching.branch (readTen a
    (radicalEquiv R ((radicalEquiv R).symm (insertTen b (HeavyCurrents.quarkEmbed q)))))).2.1 = _
  rw [Representation.Equiv.apply_symm_apply, read_insert_cross]
  split_ifs <;> simp [HeavyCurrents.branch_quarkEmbed]

theorem readU_embed (a b : Fin n) (u : Color) :
    readU R a (up R b u) = if a = b then u else 0 := by
  classical
  apply (Module.evalEquiv ℂ Color).injective
  ext f
  change (Module.evalEquiv ℂ Color) ((Module.evalEquiv ℂ Color).symm
    ((insertUp R a).dualMap (up R b u))) f = _
  rw [LinearEquiv.apply_symm_apply]
  change (ExteriorSquareBranching.branch (readTen b
    (radicalEquiv R ((radicalEquiv R).symm
      (insertTen a (ExteriorSquareBranching.tenEquiv.symm (f, 0))))))).1 u = _
  rw [Representation.Equiv.apply_symm_apply, read_insert_cross]
  by_cases h : a = b
  · subst b; simp [branch_symm]
  · simp [h, Ne.symm h]

theorem readE_embed (a b : Fin n) (e : ℂ) :
    readE R a (electron R b e) = if a = b then e else 0 := by
  classical
  apply (Module.evalEquiv ℂ ℂ).injective
  ext f
  change (Module.evalEquiv ℂ ℂ) ((Module.evalEquiv ℂ ℂ).symm
    ((insertElectron R a).dualMap (electron R b e))) f = _
  rw [LinearEquiv.apply_symm_apply]
  change (ExteriorSquareBranching.branch (readTen b
    (radicalEquiv R ((radicalEquiv R).symm
      (insertTen a (ExteriorSquareBranching.tenEquiv.symm (0, (0, f)))))))).2.2 e = _
  rw [Representation.Equiv.apply_symm_apply, read_insert_cross]
  by_cases h : a = b
  · subst b; simp [branch_symm]
  · simp [h, Ne.symm h]

def allQ : (Fin n → Quark) →ₗ[ℂ] (FullLightSpeciesQque.Q (tau R)).toSubmodule :=
  ∑ a, (Q R a).comp (LinearMap.proj a)
def allU : (Fin n → Color) →ₗ[ℂ] (FullLightSpeciesQque.U (tau R)).toSubmodule :=
  ∑ a, (U R a).comp (LinearMap.proj a)
def allE : (Fin n → ℂ) →ₗ[ℂ] (FullLightSpeciesQque.E (tau R)).toSubmodule :=
  ∑ a, (E R a).comp (LinearMap.proj a)

theorem read_allQ (a : Fin n) (x : Fin n → Quark) : readQ R a (allQ R x).val = x a := by
  classical
  simp only [allQ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.coe_sum]
  change readQ R a (∑ b, LightRadical.quark R b (x b)) = _
  simp only [map_sum, readQ_embed]
  simp
theorem read_allU (a : Fin n) (x : Fin n → Color) : readU R a (allU R x).val = x a := by
  classical
  simp only [allU, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.coe_sum]
  change readU R a (∑ b, up R b (x b)) = _
  simp only [map_sum, readU_embed]
  simp
theorem read_allE (a : Fin n) (x : Fin n → ℂ) : readE R a (allE R x).val = x a := by
  classical
  simp only [allE, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.coe_sum]
  change readE R a (∑ b, electron R b (x b)) = _
  simp only [map_sum, readE_embed]
  simp

theorem allQ_injective : Function.Injective (allQ R) := by
  intro x y h
  funext a
  simpa only [read_allQ] using congrArg (fun z => readQ R a z.val) h
theorem allU_injective : Function.Injective (allU R) := by
  intro x y h
  funext a
  simpa only [read_allU] using congrArg (fun z => readU R a z.val) h
theorem allE_injective : Function.Injective (allE R) := by
  intro x y h
  funext a
  simpa only [read_allE] using congrArg (fun z => readE R a z.val) h

theorem allQ_surjective : Function.Surjective (allQ R) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := allQ R) ?_).mp
    (allQ_injective R)
  rw [(FullLightSpeciesQque.quarkEquiv (tau R)).toLinearEquiv.finrank_eq]
  have hn := (ExactSMSpectrum.exact_species_multiplicities (hasSpectrum R)).1
  simp [Module.finrank_pi_fintype, Module.finrank_tensorProduct, ProductFactorization.MultiplicitySpace,
    hn, mul_comm]

theorem allU_surjective : Function.Surjective (allU R) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := allU R) ?_).mp
    (allU_injective R)
  rw [(FullLightSpeciesQque.upEquiv (tau R) (sm_semisimple R)).toLinearEquiv.finrank_eq]
  have hn := (ExactSMSpectrum.exact_species_multiplicities (hasSpectrum R)).2.1
  simp [Module.finrank_pi_fintype, Module.finrank_tensorProduct, Subspace.dual_finrank_eq,
    ProductFactorization.MultiplicitySpace, hn, mul_comm]

theorem allE_surjective : Function.Surjective (allE R) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := allE R) ?_).mp
    (allE_injective R)
  rw [(FullLightSpeciesQque.electronEquiv (tau R) (sm_semisimple R)).toLinearEquiv.finrank_eq]
  have hn := (ExactSMSpectrum.exact_species_multiplicities (hasSpectrum R)).2.2
  simp [Module.finrank_tensorProduct, Subspace.dual_finrank_eq,
    ProductFactorization.MultiplicitySpace, hn, mul_comm]

end
end GUT.SU5.LightSpeciesExhaustion
