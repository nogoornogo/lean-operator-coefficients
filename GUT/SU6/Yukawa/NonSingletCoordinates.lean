import GUT.SU6.Yukawa.ResidualSinglets
import GUT.SU6.Yukawa.TwoBlockSpectrum

open Math

/-! Equivariant ten/five/two-dual-five coordinates for actual matter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6NonSingletCoordinates
noncomputable section
open StandardSMUVFields StandardSMGaugeTensor SMEpsilonTensor StandardSMUVStabilizer
open SplitRepresentationProjection SU6TwoBlockSpectrum

abbrev Ten := Module.Dual ℂ Color × (Quark × Module.Dual ℂ ℂ)
abbrev Five := Color × Weak
abbrev DualFive := Module.Dual ℂ Five
abbrev Normal := Ten × ((Five × (DualFive × DualFive)) × (Fin 2 → ℂ))
abbrev Raw := (StandardSMExterior.Blocks × Module.Dual ℂ StandardSMFullGaugeMass.Heavy) ×
  Module.Dual ℂ StandardSMFullGaugeMass.Heavy

def tenRho : Representation ℂ GaugeGroup Ten :=
  upRight.dual.prod (quark.prod electronRight.dual)
def fiveRho : Representation ℂ GaugeGroup Five := (twist color (-2)).prod (twist weak 3)
def normalRho : Representation ℂ GaugeGroup Normal :=
  tenRho.prod ((fiveRho.prod (fiveRho.dual.prod fiveRho.dual)).prod
    (Representation.trivial ℂ GaugeGroup (Fin 2 → ℂ)))
def rawRho : Representation ℂ GaugeGroup Raw :=
  (StandardSMExterior.blocksRho.prod StandardSMGroup.heavy.dual).prod StandardSMGroup.heavy.dual

def antiSplit : Module.Dual ℂ StandardSMFullGaugeMass.Heavy ≃ₗ[ℂ] (DualFive × ℂ) :=
  dualSplit.trans ((LinearEquiv.refl ℂ DualFive).prodCongr singletEquiv)

theorem antiSplit_five (f : Module.Dual ℂ StandardSMFullGaugeMass.Heavy) (z : Five) :
    (antiSplit f).1 z = f (z.1, (z.2, 0)) := rfl

theorem antiSplit_singlet (f : Module.Dual ℂ StandardSMFullGaugeMass.Heavy) :
    (antiSplit f).2 = f (0, (0, 1)) := rfl

def reorder : Raw ≃ₗ[ℂ] Normal where
  toFun x := ((x.1.1.1, (x.1.1.2.1, x.1.1.2.2.1)),
    ((x.1.1.2.2.2, ((antiSplit x.1.2).1, (antiSplit x.2).1)),
      ![(antiSplit x.1.2).2, (antiSplit x.2).2]))
  invFun y := (((y.1.1, (y.1.2.1, (y.1.2.2, y.2.1.1))),
    antiSplit.symm (y.2.1.2.1, y.2.2 0)), antiSplit.symm (y.2.1.2.2, y.2.2 1))
  left_inv x := by simp
  right_inv y := by
    simp only [LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    funext i
    fin_cases i <;> rfl
  map_add' x y := by simp
  map_smul' c x := by simp

theorem reorder_five (x : Raw) : (reorder x).2.1.1 = x.1.1.2.2.2 := rfl
theorem reorder_dual (x : Raw) : (reorder x).2.1.2 =
    ((antiSplit x.1.2).1, (antiSplit x.2).1) := rfl
theorem reorder_singlet (x : Raw) : (reorder x).2.2 =
    ![(antiSplit x.1.2).2, (antiSplit x.2).2] := rfl

def assemble {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] StandardSMExterior.Blocks)
    (f : W ≃ₗ[ℂ] Module.Dual ℂ StandardSMFullGaugeMass.Heavy) :
    ((V × W) × W) ≃ₗ[ℂ] Normal := ((e.prodCongr f).prodCongr f).trans reorder

theorem assemble_five {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] StandardSMExterior.Blocks)
    (f : W ≃ₗ[ℂ] Module.Dual ℂ StandardSMFullGaugeMass.Heavy) (x : (V × W) × W) :
    (assemble e f x).2.1.1 = (e x.1.1).2.2.2 := rfl

theorem assemble_dual {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] StandardSMExterior.Blocks)
    (f : W ≃ₗ[ℂ] Module.Dual ℂ StandardSMFullGaugeMass.Heavy) (x : (V × W) × W) (z : Five) :
    (assemble e f x).2.1.2.1 z = f x.1.2 (z.1, (z.2, 0)) ∧
    (assemble e f x).2.1.2.2 z = f x.2 (z.1, (z.2, 0)) := ⟨rfl, rfl⟩

theorem assemble_singlet {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] StandardSMExterior.Blocks)
    (f : W ≃ₗ[ℂ] Module.Dual ℂ StandardSMFullGaugeMass.Heavy) (x : (V × W) × W) :
    (assemble e f x).2.2 = ![f x.1.2 (0, (0, 1)), f x.2 (0, (0, 1))] := rfl

def reorderEquiv : Representation.Equiv rawRho normalRho := .mk reorder (by
  intro g
  apply LinearMap.ext
  intro x
  ext <;> simp [reorder, rawRho, normalRho, tenRho, fiveRho, StandardSMExterior.blocksRho,
    StandardSMGroup.heavy, antiSplit, dualSplit, heavySplit, singletEquiv, Representation.dual])

private def constructedGaugeEquiv : Representation.Equiv (uvRho.comp StandardSMGroup.hom) normalRho :=
  ((prodEquiv (prodEquiv StandardSMExterior.analyticEquiv
    StandardSMGroup.analyticAntifundamentalEquiv)
    StandardSMGroup.analyticAntifundamentalEquiv).trans reorderEquiv)

private theorem gaugeEquiv_exists : ∃ e : Representation.Equiv
    (uvRho.comp StandardSMGroup.hom) normalRho, e = constructedGaugeEquiv :=
  ⟨constructedGaugeEquiv, rfl⟩

def gaugeEquiv : Representation.Equiv (uvRho.comp StandardSMGroup.hom) normalRho :=
  Classical.choose gaugeEquiv_exists

private theorem gaugeEquiv_eq : gaugeEquiv = constructedGaugeEquiv :=
  Classical.choose_spec gaugeEquiv_exists

def withResidual (H : Type*) [CommGroup H] : Representation.Equiv
    (StandardSMUVMass.rho H) (normalRho.comp (MonoidHom.fst GaugeGroup H)) :=
  restrictEquiv gaugeEquiv (MonoidHom.fst GaugeGroup H)

private theorem coords_exists : ∃ e : UV ≃ₗ[ℂ] Normal, e = gaugeEquiv.toLinearEquiv :=
  ⟨gaugeEquiv.toLinearEquiv, rfl⟩

-- Keep the analytic unitarization opaque during coordinate rewrites.
def coords : UV ≃ₗ[ℂ] Normal := Classical.choose coords_exists

theorem coords_eq : coords = gaugeEquiv.toLinearEquiv := Classical.choose_spec coords_exists

private theorem linear_action {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {rho : Representation ℂ G V} {sigma : Representation ℂ G W}
    (e : Representation.Equiv rho sigma) (g : G) (x : V) :
    e.toLinearEquiv (rho g x) = sigma g (e.toLinearEquiv x) :=
  Representation.IntertwiningMap.isIntertwining rho sigma e.toIntertwiningMap g x

theorem coords_action (H : Type*) [CommGroup H] (g : GaugeGroup × H) (x : UV) :
    coords (StandardSMUVMass.rho H g x) = normalRho g.1 (coords x) := by
  rw [coords_eq]
  exact linear_action gaugeEquiv g.1 x

private theorem antiLinear_exists : ∃ e : ConcreteSU6Representations.antifundamental.V ≃ₗ[ℂ]
    Module.Dual ℂ StandardSMFullGaugeMass.Heavy,
    e = StandardSMGroup.analyticAntifundamentalEquiv.toLinearEquiv :=
  ⟨StandardSMGroup.analyticAntifundamentalEquiv.toLinearEquiv, rfl⟩

def antiLinear := Classical.choose antiLinear_exists

theorem antiLinear_eq : antiLinear = StandardSMGroup.analyticAntifundamentalEquiv.toLinearEquiv :=
  Classical.choose_spec antiLinear_exists

theorem coords_linear : coords =
    assemble StandardSMExterior.analyticEquiv.toLinearEquiv
      antiLinear := by
  rw [antiLinear_eq]
  unfold assemble
  rw [coords_eq]
  rw [gaugeEquiv_eq]
  unfold constructedGaugeEquiv
  rw [StandardSMUVCoordinates.trans_linear, StandardSMUVCoordinates.prod_linear,
    StandardSMUVCoordinates.prod_linear]
  rfl

def fiveEquiv : Five ≃ₗ[ℂ] (Fin 5 → ℂ) where
  toFun z := ![z.1 0, z.1 1, z.1 2, z.2 0, z.2 1]
  invFun f := (![f 0, f 1, f 2], ![f 3, f 4])
  left_inv z := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  right_inv f := by funext i; fin_cases i <;> rfl
  map_add' f g := by funext i; fin_cases i <;> rfl
  map_smul' c f := by funext i; fin_cases i <;> rfl

def fiveEmbed : Five →ₗ[ℂ] Six where
  toFun z := ![z.1 0, z.1 1, z.1 2, z.2 0, z.2 1, 0]
  map_add' f g := by funext i; fin_cases i <;> simp
  map_smul' c f := by funext i; fin_cases i <;> simp

theorem fiveEmbed_value (z : Five) (i : Fin 5) :
    fiveEmbed z i.castSucc = fiveEquiv z i := by fin_cases i <;> rfl

theorem fiveEmbed_extract (z : StandardSMExterior.Blocks) :
    fiveEmbed z.2.2.2 = extract z := rfl

theorem contract_apply (w : Wedge) : contract w = extract (StandardSMExterior.branch w) := rfl

def fiveProbe (i : Fin 5) : Five := fiveEquiv.symm (Pi.single i 1)

theorem fiveEmbed_probe (i : Fin 5) : fiveEmbed (fiveProbe i) = Pi.single i.castSucc 1 := by
  funext j
  fin_cases i <;> fin_cases j <;>
    norm_num [fiveEmbed, fiveProbe, fiveEquiv, Pi.single_apply, Fin.ext_iff]

theorem anti_coordinates (f : ConcreteSU6Representations.antifundamental.V)
    (z : StandardSMFullGaugeMass.Heavy) :
    antiLinear f z =
      dualCoordinates f (StandardSMGroup.splitEquiv.symm z) := by
  rw [antiLinear_eq, StandardSMUVCoordinates.analyticAntifundamentalEquiv_linear]
  rfl

theorem coords_five (x : UV) :
    fiveEmbed (coords x).2.1.1 = contract (exteriorCoordinates x.1.1) := by
  have h := congrArg (fun e : UV ≃ₗ[ℂ] Normal => (e x).2.1.1) coords_linear
  have hh := h.trans (assemble_five StandardSMExterior.analyticEquiv.toLinearEquiv
    antiLinear x)
  exact (congrArg fiveEmbed hh).trans
    ((fiveEmbed_extract _).trans ((congrArg extract
      (StandardSMUVStabilizer.exterior_branch x.1.1)).trans (contract_apply _).symm))

theorem coords_dual_linear (x : UV) (z : Five) :
    (coords x).2.1.2.1 z =
      antiLinear x.1.2 (z.1, (z.2, 0)) ∧
    (coords x).2.1.2.2 z =
      antiLinear x.2 (z.1, (z.2, 0)) := by
  have h := assemble_dual StandardSMExterior.analyticEquiv.toLinearEquiv
    antiLinear x z
  exact ⟨(congrArg (fun e : UV ≃ₗ[ℂ] Normal => (e x).2.1.2.1 z) coords_linear).trans h.1,
    (congrArg (fun e : UV ≃ₗ[ℂ] Normal => (e x).2.1.2.2 z) coords_linear).trans h.2⟩

theorem coords_singlet_linear (x : UV) :
    (coords x).2.2 =
      ![antiLinear x.1.2 (0, (0, 1)), antiLinear x.2 (0, (0, 1))] := by
  exact (congrArg (fun e : UV ≃ₗ[ℂ] Normal => (e x).2.2) coords_linear).trans
    (assemble_singlet StandardSMExterior.analyticEquiv.toLinearEquiv
      antiLinear x)

theorem anti_five (f : ConcreteSU6Representations.antifundamental.V) (z : Five) :
    antiLinear f (z.1, (z.2, 0)) =
      dualCoordinates f (fiveEmbed z) := anti_coordinates f _

theorem anti_singlet (f : ConcreteSU6Representations.antifundamental.V) :
    antiLinear f (0, (0, 1)) =
      dualCoordinates f (Pi.single 5 1) := by
  rw [anti_coordinates, SU6YukawaLight.single_five]
  rfl

theorem coords_dual (x : UV) (z : Five) :
    (coords x).2.1.2.1 z = dualCoordinates x.1.2 (fiveEmbed z) ∧
    (coords x).2.1.2.2 z = dualCoordinates x.2 (fiveEmbed z) :=
  ⟨(coords_dual_linear x z).1.trans (anti_five x.1.2 z),
    (coords_dual_linear x z).2.trans (anti_five x.2 z)⟩

theorem coords_singlet (x : UV) :
    (coords x).2.2 = ![SU6YukawaLight.fcoord x 5, SU6YukawaLight.gcoord x 5] := by
  rw [coords_singlet_linear, anti_singlet, anti_singlet]
  rfl

theorem coords_five_value (x : UV) (i : Fin 5) :
    fiveEquiv (coords x).2.1.1 i = SU6YukawaLight.zcoord x i.castSucc := by
  rw [← fiveEmbed_value, coords_five]
  rfl

theorem coords_dual_probe (x : UV) (i : Fin 5) :
    (coords x).2.1.2.1 (fiveProbe i) = SU6YukawaLight.fcoord x i.castSucc ∧
    (coords x).2.1.2.2 (fiveProbe i) = SU6YukawaLight.gcoord x i.castSucc := by
  simpa only [fiveEmbed_probe, SU6YukawaLight.fcoord, SU6YukawaLight.gcoord] using
    coords_dual x (fiveProbe i)

theorem dual_zero_iff (f : DualFive) : f = 0 ↔ ∀ i, f (fiveProbe i) = 0 := by
  constructor
  · intro h; simp [h]
  · intro h
    have he : f.comp fiveEquiv.symm.toLinearMap = 0 := by
      apply (Pi.basisFun ℂ (Fin 5)).ext
      intro i
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply,
        LinearMap.zero_apply, fiveProbe] using h i
    apply LinearMap.ext
    intro z
    have hh := LinearMap.congr_fun he (fiveEquiv z)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.zero_apply] using hh

end
end GUT.SU6NonSingletCoordinates
