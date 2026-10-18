import GUT.SU5.Matching.LightRadicalExchange
import Physics.StandardModel.Operators.FullLightRadicalQque

open Math

/-! SM-equivariant generation maps into the unchanged radical and its dual.
Canonical evaluation images retain every generation and are H-stable. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU5.LightSpeciesMaps
noncomputable section
open Representation MatterSource GeorgiGlashowSource LightRadical
open ProductFactorization SplitRepresentationProjection StandardSMGaugeTensor
open SMEpsilonTensor StandardModelEmbedding
open scoped TensorProduct
variable {H : Type*} [Group H] {n : ℕ} (R : OrdinaryAction H n)

abbrev tau := (compatible R).action

def smEquiv : Representation.Equiv (firstRestriction (tau R)) ((gauge n).comp hom) :=
  .mk (radicalEquiv R).toLinearEquiv (by
    intro g
    apply LinearMap.ext
    intro x
    have he := (radicalEquiv R).toIntertwiningMap.isIntertwining _ _ (g, 1) x
    simpa [smAction, joint, CommutingUnitaryActions.combined_apply] using he)

theorem smEquiv_action (g : GaugeGroup) (x : Light R) :
    smEquiv R (firstRestriction (tau R) g x) = gauge n (hom g) (smEquiv R x) :=
  (smEquiv R).toIntertwiningMap.isIntertwining _ _ g x

theorem sm_continuous : ContinuousRepresentationScope.IsJointlyContinuous
    (firstRestriction (tau R)) := by
  change Continuous (fun p : GaugeGroup × Light R => firstRestriction (tau R) p.1 p.2)
  have hc := (smEquiv R).symm.toLinearMap.continuous_of_finiteDimensional.comp
    ((gauge_jointlyContinuous n).comp
      ((continuous_hom.comp continuous_fst).prodMk
        ((smEquiv R).toLinearMap.continuous_of_finiteDimensional.comp continuous_snd)))
  convert hc using 2
  rename_i p
  apply (smEquiv R).injective
  exact (smEquiv_action R p.1 p.2).trans
    ((smEquiv R).apply_symm_apply _).symm

theorem sm_semisimple : IsSemisimpleRepresentation (firstRestriction (tau R)) :=
  FullLightRadicalQque.sm_semisimple MaximalTorus.hom (joint R)
    (GeorgiGlashowSource.mass R) (compatible R) (sm_continuous R)

def readSM (a : Fin n) : IntertwiningMap (firstRestriction (tau R)) (Matter.ten.comp hom) where
  toLinearMap := (readTen a).comp (radicalEquiv R).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change readTen a (smEquiv R (firstRestriction (tau R) g x)) =
      Matter.ten (hom g) (readTen a (smEquiv R x))
    rw [smEquiv_action]
    exact UnitaryMatter.tenEquiv.symm.toIntertwiningMap.isIntertwining _ _ (hom g) _

def insertSM (a : Fin n) : IntertwiningMap (Matter.ten.comp hom) (firstRestriction (tau R)) where
  toLinearMap := (radicalEquiv R).symm.toLinearMap.comp (insertTen a)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply (smEquiv R).injective
    change smEquiv R ((smEquiv R).symm (insertTen a (Matter.ten (hom g) x))) =
      smEquiv R (firstRestriction (tau R) g ((smEquiv R).symm (insertTen a x)))
    rw [Representation.Equiv.apply_symm_apply, smEquiv_action,
      Representation.Equiv.apply_symm_apply]
    apply (WithLp.equiv 2 _).injective
    funext i
    apply (WithLp.equiv 2 _).injective
    funext b
    classical
    cases i <;> by_cases h : b = a
    all_goals simp [insertTen, gatherGenerations, MatterSource.gauge, ExplicitMultiplicity.action,
      h, constituent]
    exact UnitaryMatter.tenEquiv.toIntertwiningMap.isIntertwining _ _ (hom g) x

def quarkSM (a : Fin n) : IntertwiningMap quark (firstRestriction (tau R)) :=
  (insertSM R a).comp (ExteriorSquareBranching.tenEquiv.symm.toIntertwiningMap.comp
    ((IntertwiningMap.inr ℂ upRight.dual (quark.prod electronRight.dual)).comp
      (IntertwiningMap.inl ℂ quark electronRight.dual)))

theorem quarkSM_apply (a : Fin n) (q : Quark) : quarkSM R a q = LightRadical.quark R a q := rfl

def upProjection (a : Fin n) : IntertwiningMap (firstRestriction (tau R)) upRight.dual :=
  (IntertwiningMap.fst ℂ upRight.dual (quark.prod electronRight.dual)).comp
    (ExteriorSquareBranching.tenEquiv.toIntertwiningMap.comp (readSM R a))

def electronProjection (a : Fin n) : IntertwiningMap (firstRestriction (tau R)) electronRight.dual :=
  (IntertwiningMap.snd ℂ quark electronRight.dual).comp
    ((IntertwiningMap.snd ℂ upRight.dual (quark.prod electronRight.dual)).comp
      (ExteriorSquareBranching.tenEquiv.toIntertwiningMap.comp (readSM R a)))

def upSM (a : Fin n) : IntertwiningMap upRight (firstRestriction (tau R).dual) where
  toLinearMap := ((dualMap (upProjection R a)).comp (bidualEquiv upRight).toIntertwiningMap).toLinearMap
  isIntertwining' g := by
    have he := ((dualMap (upProjection R a)).comp
      (bidualEquiv upRight).toIntertwiningMap).isIntertwining' g
    simpa only [firstRestriction, dual_comp] using he

def electronSM (a : Fin n) : IntertwiningMap electronRight (firstRestriction (tau R).dual) where
  toLinearMap := ((dualMap (electronProjection R a)).comp
    (bidualEquiv electronRight).toIntertwiningMap).toLinearMap
  isIntertwining' g := by
    have he := ((dualMap (electronProjection R a)).comp
      (bidualEquiv electronRight).toIntertwiningMap).isIntertwining' g
    simpa only [firstRestriction, dual_comp] using he

theorem upSM_apply (a : Fin n) (u : Color) : upSM R a u = up R a u := rfl
theorem electronSM_apply (a : Fin n) (e : ℂ) : electronSM R a e = electron R a e := rfl

def Q (a : Fin n) : Quark →ₗ[ℂ] (FullLightSpeciesQque.Q (tau R)).toSubmodule :=
  (quarkSM R a).toLinearMap.codRestrict _ (fun q => FullLightSpeciesQque.quark_mem _ _ q)

def U (a : Fin n) : Color →ₗ[ℂ] (FullLightSpeciesQque.U (tau R)).toSubmodule :=
  (upSM R a).toLinearMap.codRestrict _ (fun u => FullLightSpeciesQque.up_mem _ _ u)

def E (a : Fin n) : ℂ →ₗ[ℂ] (FullLightSpeciesQque.E (tau R)).toSubmodule :=
  (electronSM R a).toLinearMap.codRestrict _ (fun e => FullLightSpeciesQque.electron_mem _ _ e)

end
end GUT.SU5.LightSpeciesMaps
