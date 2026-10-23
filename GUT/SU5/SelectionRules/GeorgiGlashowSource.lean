import GUT.SU5.SelectionRules.MatterSource
import GUT.SU5.Embeddings.PhysicalTorus
import GUT.Common.StandardChain.ConjugationAdapter
import Physics.StandardModel.Operators.BaryonOne.Qque.ExactSMSpectrumQque

open Physics

open Math

/-! The retained Georgi-Glashow fermion sector with a possibly non-Abelian
centralizer action. Zero mass is a pre-electroweak benchmark, not a claim
about a dynamically selected vacuum or Yukawa couplings. -/

namespace GUT.SU5.GeorgiGlashowSource
open Physics.SU5
set_option autoImplicit false
noncomputable section
open Representation MatterSource StandardModelEmbedding InvariantWeylMass
open ContinuousRepresentationScope ProductFactorization

variable {H : Type*} [Group H] {n : ℕ} (R : OrdinaryAction H n)

def residual : Representation ℂ H (Space n) where
  toFun h := (R h).val.val.toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    change (R 1).val.val x = x
    rw [R.map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change (R (g * h)).val.val x = (R g).val.val ((R h).val.val x)
    rw [R.map_mul]
    rfl

theorem residual_commutes (g : TargetGroup) (h : H) :
    Commute (gauge n g) (residual R h) := by
  apply LinearMap.ext
  intro x
  exact (congrArg (fun f : Space n →L[ℂ] Space n => f x) ((R h).property g).eq).symm

def joint : Representation ℂ (TargetGroup × H) (Space n) :=
  CommutingUnitaryActions.combined (gauge n) (residual R) (residual_commutes R)

theorem joint_restrict_gauge : (joint R).comp (MonoidHom.inl TargetGroup H) = gauge n :=
  CommutingUnitaryActions.combined_restrict_left _ _ _

def mass := SymmetricMass.zero ((joint R).comp (MaximalTorus.hom.prodMap (MonoidHom.id H)))

def smAction : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) (Space n) :=
  (joint R).comp (hom.prodMap (MonoidHom.id H))

theorem sm_restriction :
    (smAction R).comp (PhysicalTorus.gaugeHom.prodMap (MonoidHom.id H)) =
      ((joint R).comp (MaximalTorus.hom.prodMap (MonoidHom.id H))).comp
        (PhysicalTorus.toTorus.prodMap (MonoidHom.id H)) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  change joint R (hom (PhysicalTorus.gaugePoint g.1), g.2) x = _
  rw [PhysicalTorus.hom_gaugePoint]
  rfl

def compatible : LightSMAction.Compatible MaximalTorus.hom (joint R) (mass R) :=
  LightSMAction.ofInvariantMass _ _ _ (smAction R) (by intros; rfl) (sm_restriction R)

def radicalEquiv : Equiv (compatible R).action (smAction R) :=
  .mk (SymmetricMass.zeroRadicalEquiv
    ((joint R).comp (MaximalTorus.hom.prodMap (MonoidHom.id H)))).toLinearEquiv
    (by intro g; rfl)

def generationReorder : (ExteriorSquareBranching.Blocks × FundamentalBranching.BarBlocks)
    ≃ₗ[ℂ] ExactSMSpectrum.Generation where
  toFun x := (x.1.2.1, x.1.1, x.2.1, x.2.2, x.1.2.2)
  invFun y := ((y.2.1, y.1, y.2.2.2.2), (y.2.2.1, y.2.2.2.1))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def generationRepresentationEquiv : Equiv
    (Representation.prod ((constituent .ten).comp hom) ((constituent .barFive).comp hom))
    ExactSMSpectrum.generation :=
  (SplitRepresentationProjection.prodEquiv UnitaryBranching.tenEquiv
    UnitaryBranching.antifundamentalEquiv).trans
    (.mk generationReorder (by intro g; rfl))

def gatherGenerations (n : ℕ) : Space n ≃ₗ[ℂ] (Fin n → Carrier .ten × Carrier .barFive) where
  toFun x a := (x .ten a, x .barFive a)
  invFun y := WithLp.toLp 2 fun i => WithLp.toLp 2 fun a => match i with
    | .ten => (y a).1
    | .barFive => (y a).2
  left_inv x := by
    apply (WithLp.equiv 2 _).injective
    funext i
    apply (WithLp.equiv 2 _).injective
    funext a
    cases i <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def gatherRepresentationEquiv (n : ℕ) : Equiv ((gauge n).comp hom)
    (FiniteSpectrum.copies n (Representation.prod ((constituent .ten).comp hom)
      ((constituent .barFive).comp hom))) :=
  .mk (gatherGenerations n) (by intro g; rfl)

private def copiesEquiv {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {r : Representation ℂ G V} {s : Representation ℂ G W}
    (n : ℕ) (e : Equiv r s) : Equiv (FiniteSpectrum.copies n r) (FiniteSpectrum.copies n s) :=
  .mk (LinearEquiv.piCongrRight fun _ => e.toLinearEquiv) (by
    intro g
    apply LinearMap.ext
    intro x
    funext a
    exact e.toIntertwiningMap.isIntertwining _ _ g (x a))

def noSingletsEquiv (n : ℕ) : Equiv (FiniteSpectrum.copies n ExactSMSpectrum.generation)
    (ExactSMSpectrum.action n 0) :=
  .mk (LinearEquiv.prodUnique (R := ℂ) (M := Fin n → ExactSMSpectrum.Generation)
    (M₂ := Fin 0 → ℂ)).symm (by
      intro g
      apply LinearMap.ext
      intro x
      exact Prod.ext rfl (Subsingleton.elim _ _))

def spectrumEquiv (n : ℕ) : Equiv ((gauge n).comp hom) (ExactSMSpectrum.action n 0) :=
  ((gatherRepresentationEquiv n).trans (copiesEquiv n generationRepresentationEquiv)).trans
    (noSingletsEquiv n)

theorem sm_gauge : firstRestriction (smAction R) = (gauge n).comp hom := by
  apply MonoidHom.ext
  intro g
  exact DFunLike.congr_fun (joint_restrict_gauge R) (hom g)

def actualSpectrumEquiv : Equiv (firstRestriction (compatible R).action)
    (ExactSMSpectrum.action n 0) := by
  have e := SplitRepresentationProjection.restrictEquiv (radicalEquiv R)
    (MonoidHom.inl _ H)
  change Equiv (firstRestriction (compatible R).action) (firstRestriction (smAction R)) at e
  rw [sm_gauge R] at e
  exact e.trans (spectrumEquiv n)

theorem hasSpectrum : ExactSMSpectrum.HasSpectrum
    (firstRestriction (compatible R).action) n 0 := ⟨actualSpectrumEquiv R⟩

theorem torus_unitary : UnitaryMultiplicity.IsUnitaryRepresentation
    (ResidualWeightSpace.torus ((joint R).comp (MaximalTorus.hom.prodMap (MonoidHom.id H)))) := by
  intro t x y
  have he := LinearMap.congr_fun (DFunLike.congr_fun (joint_restrict_gauge R)
    (MaximalTorus.hom t))
  change ∀ x, joint R (MaximalTorus.hom t, 1) x = gauge n (MaximalTorus.hom t) x at he
  change inner ℂ (joint R (MaximalTorus.hom t, 1) x)
    (joint R (MaximalTorus.hom t, 1) y) = _
  rw [he x, he y]
  exact gauge_unitary n _ x y

variable [TopologicalSpace H]

theorem joint_continuous (hR : Continuous R) : IsJointlyContinuous (joint R) := by
  apply CommutingUnitaryActions.combined_jointlyContinuous
  · exact gauge_jointlyContinuous n
  · exact ((continuous_subtype_val.comp (continuous_subtype_val.comp hR)).comp
      continuous_fst).clm_apply continuous_snd

theorem compatible_continuous (hR : Continuous R) :
    IsJointlyContinuous (compatible R).action := by
  apply LightSMAction.ofInvariantMass_continuous
  exact (joint_continuous R hR).comp
    (StandardModelEmbedding.continuousHom.prodMap (ContinuousMonoidHom.id H))

variable [IsTopologicalGroup H] [CompactSpace H]

theorem exists_actual_exterior (hR : Continuous R) (hn : 0 < n) :
    LightSMSpeciesQque.HasActualExterior MaximalTorus.hom (joint R) (mass R) (compatible R) :=
  ExactSMSpectrumQque.exists_actual_exterior _ _ _ _ (hasSpectrum R) hn (torus_unitary R)
    (compatible_continuous R hR)
    (StandardChainConjugation.threeConjugations (MonoidHom.id TargetGroup)).toTwo

end
end GUT.SU5.GeorgiGlashowSource
