import GUT.SUN.SelectionRules.StandardChain
import GUT.SUN.Branching.RankSeven
import GUT.SU5.SelectionRules.StandardChainBenchmark

open Physics

open Math Math.SUN

/-! A continuous actual SU(7) inhabitant: Lambda^2(7) + 3 bar7 has
dimension 42. Its restricted dual index is one neutral SM generation.
Zero mass leaves additional vectorlike fields and singlets in the radical;
the exact *dual* target deliberately allows these. -/

set_option autoImplicit false

namespace GUT.SUN.RankSevenBenchmark


noncomputable section

open SU5 InvariantWeylMass FiniteAbelianChargeSectors

abbrev DualPair := WithLp 2 (Matter.CovectorHilbert 7 × Matter.CovectorHilbert 7)
abbrev DualTriple := WithLp 2 (Matter.CovectorHilbert 7 × DualPair)
abbrev Space := WithLp 2 (Matter.WedgeHilbert 7 × DualTriple)

def dualPair : Representation ℂ (Block.Group 7) DualPair :=
  HilbertProductRepresentation.action (Matter.unitaryDual 7).toRepresentation
    (Matter.unitaryDual 7).toRepresentation

def dualTriple : Representation ℂ (Block.Group 7) DualTriple :=
  HilbertProductRepresentation.action (Matter.unitaryDual 7).toRepresentation dualPair

def ambient : Representation ℂ (Block.Group 7) Space :=
  HilbertProductRepresentation.action (Matter.unitaryWedge 7).toRepresentation dualTriple

theorem ambient_unitary : UnitaryMultiplicity.IsUnitaryRepresentation ambient :=
  HilbertProductRepresentation.unitary _ _ (Matter.wedge_unitary 7).inner_map_map
    (HilbertProductRepresentation.unitary _ _ (Matter.dual_unitary 7).inner_map_map
      (HilbertProductRepresentation.unitary _ _ (Matter.dual_unitary 7).inner_map_map
        (Matter.dual_unitary 7).inner_map_map))

theorem ambient_continuous : Continuous (fun p : Block.Group 7 × Space => ambient p.1 p.2) := by
  have hd : Continuous (fun p : Block.Group 7 × Matter.CovectorHilbert 7 =>
      Matter.unitaryDual 7 p.1 p.2) :=
    ((Matter.dual_continuous 7).comp continuous_fst).clm_apply continuous_snd
  have hw : Continuous (fun p : Block.Group 7 × Matter.WedgeHilbert 7 =>
      Matter.unitaryWedge 7 p.1 p.2) :=
    ((Matter.wedge_continuous 7).comp continuous_fst).clm_apply continuous_snd
  exact HilbertProductRepresentation.jointlyContinuous _ _ hw
    (HilbertProductRepresentation.jointlyContinuous _ _ hd
      (HilbertProductRepresentation.jointlyContinuous _ _ hd hd))

theorem ambient_character (t : MaximalTorus.Torus) :
    ambient.character (Block.inclusion 5 2 (MaximalTorus.hom t)) =
      UnitaryMatter.ten.toRepresentation.character (MaximalTorus.hom t) +
        2 * (∑ i : Fin 5, (t.val i : ℂ)) +
        3 * UnitaryMatter.antifundamental.toRepresentation.character (MaximalTorus.hom t) + 7 := by
  simp only [ambient, dualTriple, dualPair, HilbertProductRepresentation.character,
    RankSeven.wedge_restriction, RankSeven.dual_restriction]
  ring

variable (H : Type*) [CommGroup H]

def rho : Representation ℂ (Block.Group 7 × H) Space :=
  ambient.comp (MonoidHom.fst _ _)

theorem restricted_index (g : TorusCharacter.CombinedGroup H) :
    (rho H).character (Block.inclusion 5 2 (MaximalTorus.hom g.1), g.2) -
        (rho H).character (Block.inclusion 5 2 (MaximalTorus.hom g.1⁻¹), g.2⁻¹) =
      (StandardChainBenchmark.rho (0 : ChargeLabel H) 0).character (MaximalTorus.hom g.1, g.2) -
        (StandardChainBenchmark.rho (0 : ChargeLabel H) 0).character
          (MaximalTorus.hom g.1⁻¹, g.2⁻¹) := by
  change ambient.character (Block.inclusion 5 2 (MaximalTorus.hom g.1)) -
    ambient.character (Block.inclusion 5 2 (MaximalTorus.hom g.1⁻¹)) = _
  rw [ambient_character, ambient_character]
  rw [congrFun (Representation.char_iso (StandardChainBenchmark.pairEquiv (0 : ChargeLabel H) 0)) _,
    congrFun (Representation.char_iso (StandardChainBenchmark.pairEquiv (0 : ChargeLabel H) 0)) _]
  simp only [StandardChainBenchmark.pairAction, TorusMatterCharacter.character_prod,
    CommutingUnitaryActions.charged_character]
  have hb := RankSeven.bar_five_character g.1
  have hi := RankSeven.bar_five_character g.1⁻¹
  simp only [Subgroup.coe_inv, Pi.inv_apply, inv_inv] at hi
  rw [hb, hi]
  have hz (h : H) : ((0 : ChargeLabel H).toMul h : ℂ) = 1 := rfl
  simp only [hz, one_mul, Subgroup.coe_inv, Pi.inv_apply]
  ring

theorem hasTarget (B : SymmetricMass ((rho H).comp
    (GUT.StandardChain.torusInclusion (StandardChain.inclusion 2)))) :
    TorusMassSource.HasTarget (GUT.StandardChain.pullback (StandardChain.inclusion 2) (rho H))
      B (StandardChainBenchmark.family (0 : ChargeLabel H) 0).profiles 0 := by
  intro g
  refine (B.radical_dual_character_eq g).trans ?_
  rw [Representation.char_dual]
  change (rho H).character (Block.inclusion 5 2 (MaximalTorus.hom g.1), g.2) -
      (rho H).character (Block.inclusion 5 2 (MaximalTorus.hom g.1⁻¹), g.2⁻¹) = _
  rw [restricted_index]
  have ht := TorusMassSource.source_target (StandardChainBenchmark.rho (0 : ChargeLabel H) 0)
    (SymmetricMass.zero _) _ _ (StandardChainBenchmark.hasTarget _ _ _) g
  rw [Representation.char_dual] at ht
  exact ht

def model : StandardChain.Model 2 (rho H) where
  unitary := fun g => ambient_unitary g.1
  mass := SymmetricMass.zero _
  profile := StandardChainBenchmark.family (0 : ChargeLabel H) 0
  singlets := 0
  lightTarget := hasTarget H _

theorem rho_continuous [TopologicalSpace H] :
    Continuous (fun p : (Block.Group 7 × H) × Space => rho H p.1 p.2) := by
  change Continuous (fun p : (Block.Group 7 × H) × Space => ambient p.1.1 p.2)
  have hc : Continuous (fun p : (Block.Group 7 × H) × Space => (p.1.1, p.2)) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  exact Continuous.comp (f := fun p : (Block.Group 7 × H) × Space => (p.1.1, p.2))
    (g := fun p : Block.Group 7 × Space => ambient p.1 p.2) ambient_continuous hc

def continuousModel [TopologicalSpace H] [IsTopologicalGroup H] :
    GUT.StandardChain.ContinuousModel (StandardChain.inclusion 2) (rho H) :=
  StandardChain.continuousModel (k := 2) (rho := rho H) (model H)
    (rho_continuous H)

theorem finrank_space : Module.finrank ℂ Space = 42 := by
  have hd : Module.finrank ℂ (Matter.CovectorHilbert 7) = 7 := by
    rw [← (Matter.dualEquiv 7).toLinearEquiv.finrank_eq]
    simp [Matter.Covector, Matter.Vector, Subspace.dual_finrank_eq]
  have hw : Module.finrank ℂ (Matter.WedgeHilbert 7) = 21 := by
    rw [← (Matter.wedgeEquiv 7).toLinearEquiv.finrank_eq]
    simp [Matter.Wedge, Matter.Vector, exteriorPower.finrank_eq, Nat.choose]
  simp only [Space, DualTriple, DualPair, (WithLp.linearEquiv 2 ℂ _).finrank_eq,
    Module.finrank_prod, hd, hw]

theorem radical_finrank : Module.finrank ℂ (model H).mass.radical.toSubmodule = 42 := by
  have ht : (model H).mass.radical.toSubmodule = ⊤ := by
    apply top_unique
    intro x _
    change (model H).mass.form x = 0
    rfl
  rw [ht, finrank_top, finrank_space]

theorem nonvacuous :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      (model H).lightSpectrum := (model H).selection_rule_obstruction

end

end GUT.SUN.RankSevenBenchmark
