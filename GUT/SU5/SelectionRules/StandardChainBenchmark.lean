import GUT.Common.StandardChain.StandardChain
import GUT.SU5.Branching.TorusMatterCharacter
import Math.RepresentationTheory.Decomposition.HilbertProductRepresentation

open Math

/-! A positive actual-source inhabitant of the standard-chain interface.
The fields are the existing continuous unitary 10 and bar5. Independent
residual characters may be nontrivial or have finite order. The mass is zero;
this example does not assert a nonzero coupling or realistic flavor data. -/

set_option autoImplicit false

namespace GUT.SU5.StandardChainBenchmark

noncomputable section

open StandardModelEmbedding FiniteAbelianChargeSectors StandardAbelianCharge
open StandardSMCharacterTarget InvariantWeylMass StandardWeylDualTarget
open TorusMatterCharacter CommutingUnitaryActions

abbrev Space := WithLp 2 (UnitaryMatter.TenHilbert × UnitaryMatter.BarFiveHilbert)

variable {H : Type*} [CommGroup H] (q r : ChargeLabel H)

def pairAction : Representation ℂ (TargetGroup × H)
    (UnitaryMatter.TenHilbert × UnitaryMatter.BarFiveHilbert) :=
  (charged UnitaryMatter.ten.toRepresentation q.toMul).prod
    (charged UnitaryMatter.antifundamental.toRepresentation r.toMul)

def rho : Representation ℂ (TargetGroup × H) Space :=
  HilbertProductRepresentation.action
    (charged UnitaryMatter.ten.toRepresentation q.toMul)
    (charged UnitaryMatter.antifundamental.toRepresentation r.toMul)

def pairEquiv : Representation.Equiv (rho q r) (pairAction q r) :=
  HilbertProductRepresentation.equiv _ _

theorem unitary : UnitaryMultiplicity.IsUnitaryRepresentation (rho q r) :=
  HilbertProductRepresentation.unitary _ _
    (charged_unitary _ _ UnitaryMatter.ten_unitary.inner_map_map)
    (charged_unitary _ _ UnitaryMatter.antifundamental_unitary.inner_map_map)

theorem character (g : TorusCharacter.CombinedGroup H) :
    (TorusCharacterSource.restrict (rho q r)).character g =
      TorusCharacter.eval (exactSMResolvedCharacter 1 (sectorCharges q r)) g := by
  change (rho q r).character (MaximalTorus.hom g.1, g.2) = _
  rw [congrFun (Representation.char_iso (pairEquiv q r)) _]
  rw [pairAction, character_prod, charged_character, charged_character]
  simpa only [mul_comm] using charged_pair_character q r g.1 g.2

def family : FiniteChargeProfiles.Family (ChargeLabel H) :=
  ⟨FiniteChargeProfiles.pure 1 (sectorCharges q r), 1, by decide,
    FiniteChargeProfiles.pure_totals _ _⟩

theorem hasTarget (B : SymmetricMass (TorusCharacterSource.restrict (rho q r))) :
    TorusMassSource.HasTarget (rho q r) B (family q r).profiles 0 := by
  intro g
  rw [B.radical_dual_character_eq, Representation.char_dual, character, character]
  change _ = TorusCharacter.eval
    (chiralDifference (FiniteChargeProfiles.targetWithSinglets
      (FiniteChargeProfiles.pure 1 (sectorCharges q r)) 0)) g
  rw [FiniteChargeProfiles.targetWithSinglets_pure]
  simp only [exactSMWithSingletsResolvedCharacter, singletResolvedCharacter,
    Finsupp.mapDomain_zero, add_zero, Int.natCast_one, TorusCharacter.eval_chiralDifference]

def model : StandardChain.Model (MonoidHom.id TargetGroup) (rho q r) where
  unitary := unitary q r
  mass := SymmetricMass.zero _
  profile := family q r
  singlets := 0
  lightTarget := hasTarget q r _

theorem nonvacuous :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      (model q r).lightSpectrum :=
  (model q r).selection_rule_obstruction

theorem finrank_space : Module.finrank ℂ Space = 15 := by
  rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq, Module.finrank_prod]
  simp

theorem radical_top : (model q r).mass.radical.toSubmodule = ⊤ := by
  apply top_unique
  intro x _
  change (model q r).mass.form x = 0
  rfl

theorem radical_finrank : Module.finrank ℂ (model q r).mass.radical.toSubmodule = 15 := by
  rw [radical_top, finrank_top, finrank_space]

def continuousModel [TopologicalSpace H] [IsTopologicalGroup H]
    (hq : Continuous q.toMul) (hr : Continuous r.toMul) :
    StandardChain.ContinuousModel (MonoidHom.id TargetGroup) (rho q r) where
  toModel := model q r
  inclusion_injective := Function.injective_id
  inclusion_continuous := continuous_id
  action_continuous := HilbertProductRepresentation.jointlyContinuous _ _
    (charged_jointlyContinuous _ _ hq
      ((UnitaryMatter.ten_continuous.comp continuous_fst).clm_apply continuous_snd))
    (charged_jointlyContinuous _ _ hr
      ((UnitaryMatter.antifundamental_continuous.comp continuous_fst).clm_apply continuous_snd))

end

end GUT.SU5.StandardChainBenchmark
