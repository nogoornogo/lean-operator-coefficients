import GUT.SU6.Boundary.ChiralSelection
import GUT.SU6.Adapters.StandardScalarBlock
import GUT.SU6.Characters.AmbientTorus
import Math.RepresentationTheory.Weights.CyclicCharge

/-! The integral double cover of the residual baryon phase: the defining
six transforms by diag(z² I₃,I₂,1), so its character degree is 6B.
This is a central degree phase times an actual SU(6) compensator. -/
namespace GUT.SU6BoundaryBaryon
set_option autoImplicit false
noncomputable section
open Math Physics StandardSMGaugeTensor SMEpsilonTensor StandardSMExterior
open scoped TensorProduct

private def torusLift : Circle →* AmbientTorus.Torus where
  toFun z := ![z,z,z,z⁻¹,z⁻¹]
  map_one' := by ext i; fin_cases i <;> simp
  map_mul' z w := by ext i; fin_cases i <;> simp [mul_comm]

def compensator : Circle →* ActualRestriction.SU6 := AmbientTorus.toSU6MonoidHom.comp torusLift

theorem compensator_diagonal (z : Circle) :
    (compensator z : Matrix (Fin 6) (Fin 6) ℂ) =
      Matrix.diagonal (StandardScalarBlock.coords (z : ℂ) (↑z⁻¹ : ℂ) (↑z⁻¹ : ℂ)) := by
  change Matrix.diagonal (AmbientTorus.coords (torusLift z)) = _
  congr 1
  ext i
  fin_cases i <;>
    simp [AmbientTorus.coords,AmbientTorus.circleCoords,torusLift,StandardScalarBlock.coords,
      Fin.prod_univ_succ]

/-- Residual action in split defining coordinates. -/
def splitAction : Representation ℂ Circle Six where
  toFun z :=
    { toFun := fun x => ((z : ℂ)^2 • x.1, x.2)
      map_add' _ _ := by simp [smul_add]
      map_smul' a x := by simp [smul_smul,mul_comm] }
  map_one' := by ext x <;> simp
  map_mul' z w := by ext x <;> simp [mul_pow,smul_smul]

/-- The actual defining action, transported through the fixed coordinate split. -/
def defining : Representation ℂ Circle SU6BoundaryCube.Vector :=
  { toFun := fun z => StandardSMGroup.splitEquiv.symm.toLinearMap.comp
      ((splitAction z).comp StandardSMGroup.splitEquiv.toLinearMap)
    map_one' := by
      apply LinearMap.ext; intro v
      simp
    map_mul' := by
      intro z w
      apply LinearMap.ext; intro v
      simp [map_mul,LinearMap.comp_apply] }

theorem defining_action (z : Circle) (v : SU6BoundaryCube.Vector) :
    StandardSMGroup.splitEquiv (defining z v) = splitAction z (StandardSMGroup.splitEquiv v) := by
  change StandardSMGroup.splitEquiv (StandardSMGroup.splitEquiv.symm _) = _
  rw [StandardSMGroup.splitEquiv.apply_symm_apply]
  rfl

theorem compensator_factor (z : Circle) (v : SU6BoundaryCube.Vector) :
    defining z v = (z : ℂ) • FundamentalRepresentation.rho (compensator z) v := by
  apply StandardSMGroup.splitEquiv.injective
  rw [defining_action,map_smul,StandardScalarBlock.fundamental_action
    (compensator z) _ _ _ (compensator_diagonal z)]
  change ((z : ℂ)^2 • _, _) = _
  simp [StandardScalarBlock.six, smul_smul, pow_two, Circle.coe_inv,
    Circle.coe_ne_zero]

/-- Exterior functoriality proves all central degree phases at once. -/
theorem exterior_factor (n : ℕ) (z : Circle) (v : ⋀[ℂ]^n SU6BoundaryCube.Vector) :
    defining.exteriorPower n z v =
      (z : ℂ)^n • exteriorPower.map n (FundamentalRepresentation.rho (compensator z)) v := by
  have he : exteriorPower.map n (defining z) =
      (z : ℂ)^n • exteriorPower.map n (FundamentalRepresentation.rho (compensator z)) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
      LinearMap.smul_apply]
    change exteriorPower.ιMulti ℂ n (fun i => defining z (f i)) = _
    simp_rw [compensator_factor]
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Function.comp_def] using
      (exteriorPower.ιMulti ℂ n).map_smul_univ
      (fun _ => (z : ℂ)) (fun i => FundamentalRepresentation.rho (compensator z) (f i))
  exact LinearMap.congr_fun he v

theorem six_scalar (z : Circle) (x : Six) :
    splitAction z x = ((z : ℂ)^2 • x.1,x.2) := rfl

theorem scalar_vev_fixed (z : Circle) (a : ℂ) : splitAction z (0,(0,a)) = (0,(0,a)) := by
  simp [splitAction]

theorem weak_fixed (z : Circle) (w : Weak) : splitAction z (0,(w,0)) = (0,(w,0)) := by
  simp [splitAction]

/-- The weak plus singlet subspace is fixed pointwise. -/
theorem weak_singlet_fixed (z : Circle) (w : Weak) (a : ℂ) :
    splitAction z (0,(w,a)) = (0,(w,a)) := by simp [splitAction]

def blocksAction (z : Circle) : Blocks →ₗ[ℂ] Blocks :=
  StandardScalarBlock.blocksLinear ((z : ℂ)^2) 1 1

theorem branch_action (z : Circle) (v : SU6BoundaryCube.Square) :
    branch (defining.exteriorPower 2 z v) = blocksAction z (branch v) := by
  have he : branch.comp (defining.exteriorPower 2 z) = (blocksAction z).comp branch := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    change branch (exteriorPower.map 2 (defining z) (exteriorPower.ιMulti ℂ 2 f)) = _
    rw [exteriorPower.map_apply_ιMulti,StandardSMExterior.branch_wedge]
    change _ = StandardScalarBlock.blocks ((z : ℂ)^2) 1 1
      (branch (exteriorPower.ιMulti ℂ 2 f))
    rw [StandardSMExterior.branch_wedge]
    change pair (StandardSMGroup.splitEquiv (defining z (f 0)))
      (StandardSMGroup.splitEquiv (defining z (f 1))) = _
    rw [defining_action,defining_action]
    change pair (((z : ℂ)^2 • (StandardSMGroup.splitEquiv (f 0)).1),
      (StandardSMGroup.splitEquiv (f 0)).2)
      (((z : ℂ)^2 • (StandardSMGroup.splitEquiv (f 1)).1),
      (StandardSMGroup.splitEquiv (f 1)).2) = _
    simpa only [StandardScalarBlock.six,one_smul,one_mul] using
      StandardScalarBlock.pair_action ((z : ℂ)^2) 1 1
        (StandardSMGroup.splitEquiv (f 0)) (StandardSMGroup.splitEquiv (f 1))
  exact LinearMap.congr_fun he v

theorem left15_charges (z : Circle) (x : SU6BoundarySelection.Light15) :
    blocksAction z (SU6BoundarySelection.embed15 x) =
      SU6BoundarySelection.embed15 ((z : ℂ)^2 • x.1,x.2) := by
  change StandardScalarBlock.blocks ((z : ℂ)^2) 1 1 _ = _
  simp [StandardScalarBlock.blocks, SU6BoundarySelection.embed15]

theorem boundaries15 (z : Circle) :
    SU6BoundarySelection.uv15.comp (blocksAction z) = (blocksAction z).comp SU6BoundarySelection.uv15 ∧
    SU6BoundarySelection.ir15.comp (blocksAction z) = (blocksAction z).comp SU6BoundarySelection.ir15 := by
  have h (c w t : ℂ) :
      SU6BoundarySelection.uv15.comp (StandardScalarBlock.blocksLinear c w t) =
        (StandardScalarBlock.blocksLinear c w t).comp SU6BoundarySelection.uv15 ∧
      SU6BoundarySelection.ir15.comp (StandardScalarBlock.blocksLinear c w t) =
        (StandardScalarBlock.blocksLinear c w t).comp SU6BoundarySelection.ir15 := by
    constructor <;> apply LinearMap.ext <;> intro x
    · change ((c*c) • x.1, ((c*w) • x.2.1, ((w*w) • x.2.2.1, (0,0)))) =
        ((c*c) • x.1, ((c*w) • x.2.1, ((w*w) • x.2.2.1, ((c*t) • 0,(w*t) • 0))))
      simp only [smul_zero]
    · change (0, ((c*w) • x.2.1, ((w*w) • x.2.2.1, ((c*t) • x.2.2.2.1,(w*t) • x.2.2.2.2)))) =
        ((c*c) • 0, ((c*w) • x.2.1, ((w*w) • x.2.2.1, ((c*t) • x.2.2.2.1,(w*t) • x.2.2.2.2))))
      simp only [smul_zero]
  exact h ((z : ℂ)^2) 1 1

theorem boundary6 (z : Circle) :
    SU6BoundarySelection.singletProjection.comp (splitAction z) =
      (splitAction z).comp SU6BoundarySelection.singletProjection := by
  ext x <;> simp [SU6BoundarySelection.singletProjection,splitAction]

theorem color_action (z : Circle) (x : Color) :
    defining z (SU6BoundaryCube.colorIn x) = (z : ℂ)^2 • SU6BoundaryCube.colorIn x := by
  apply StandardSMGroup.splitEquiv.injective
  rw [defining_action,map_smul]
  simp [SU6BoundaryCube.colorIn,splitAction]

theorem weak_action (z : Circle) (w : Weak) :
    defining z (SU6BoundaryCube.weakIn w) = SU6BoundaryCube.weakIn w := by
  apply StandardSMGroup.splitEquiv.injective
  rw [defining_action]
  simp [SU6BoundaryCube.weakIn,splitAction]

theorem right20_charge (z : Circle) (x : Color) :
    defining.exteriorPower 3 z (SU6BoundaryCube.embed x) = (z : ℂ)^2 • SU6BoundaryCube.embed x := by
  rw [SU6BoundaryCube.embed_cube]
  change exteriorPower.map 3 (defining z) _ = _
  rw [← ExteriorCubeHook.cube_natural,color_action,weak_action,weak_action]
  exact (exteriorPower.ιMulti ℂ 3).map_vecCons_smul _ _ _

private theorem area_action (z : Circle) (x : SU6BoundaryCube.Square) :
    SU6BoundaryCube.area (defining.exteriorPower 2 z x) = SU6BoundaryCube.area x := by
  change (branch (defining.exteriorPower 2 z x)).2.2.1 1 = _
  rw [branch_action]
  change ((1 * 1 : ℂ) • (branch x).2.2.1) 1 = _
  simp [SU6BoundaryCube.area]

private theorem colorOut_action (z : Circle) (x : SU6BoundaryCube.Vector) :
    SU6BoundaryCube.colorOut (defining z x) = (z : ℂ)^2 • SU6BoundaryCube.colorOut x :=
  congrArg Prod.fst (defining_action z x)

theorem contract_action (z : Circle) (x : SU6BoundaryCube.Cube) :
    SU6BoundaryCube.contract (defining.exteriorPower 3 z x) =
      (z : ℂ)^2 • SU6BoundaryCube.contract x := by
  let t := (TensorProduct.rid ℂ Color).toLinearMap.comp
    (TensorProduct.map SU6BoundaryCube.colorOut SU6BoundaryCube.area)
  have ht : t.comp (TensorProduct.map (defining z) (defining.exteriorPower 2 z)) =
      (z : ℂ)^2 • t := by
    apply TensorProduct.ext'; intro a b
    change SU6BoundaryCube.area (defining.exteriorPower 2 z b) •
      SU6BoundaryCube.colorOut (defining z a) =
      (z : ℂ)^2 • (SU6BoundaryCube.area b • SU6BoundaryCube.colorOut a)
    rw [area_action,colorOut_action,smul_comm]
  change t (ExteriorCubeHook.coproduct (exteriorPower.map 3 (defining z) x)) = _
  rw [ExteriorCubeHook.coproduct_natural]
  exact LinearMap.congr_fun ht (ExteriorCubeHook.coproduct x)

theorem boundary20 (z : Circle) :
    SU6BoundarySelection.twenty.ir.comp (defining.exteriorPower 3 z) =
      (defining.exteriorPower 3 z).comp SU6BoundarySelection.twenty.ir := by
  apply LinearMap.ext; intro x
  change defining.exteriorPower 3 z x -
      SU6BoundaryCube.embed (SU6BoundaryCube.contract (defining.exteriorPower 3 z x)) =
    defining.exteriorPower 3 z (x - SU6BoundaryCube.embed (SU6BoundaryCube.contract x))
  rw [map_sub,contract_action,right20_charge,map_smul]

theorem defining_gauge_commutes (z : Circle) (g : GaugeGroup) :
    (defining z).comp (FundamentalRepresentation.rho (StandardSMGroup.hom g)) =
      (FundamentalRepresentation.rho (StandardSMGroup.hom g)).comp (defining z) := by
  apply LinearMap.ext; intro x
  apply StandardSMGroup.splitEquiv.injective
  rw [LinearMap.comp_apply,LinearMap.comp_apply,defining_action,
    StandardSMGroup.splitEquiv_action,StandardSMGroup.splitEquiv_action,defining_action]
  change ((z : ℂ)^2 • twist color (-2) g _, _) = _
  simp [StandardSMGroup.heavy,splitAction]

def higgsEntry (w : Weak) : SU6BoundaryCube.Vector →ₗ[ℂ] SU6BoundaryCube.Vector :=
  (SU6BoundaryCube.weakIn.comp (LinearMap.toSpanSingleton ℂ Weak w)).comp
    ((LinearMap.snd ℂ Weak ℂ).comp
      ((LinearMap.snd ℂ Color (Weak × ℂ)).comp StandardSMGroup.splitEquiv.toLinearMap))

/-- The actual weak--singlet endomorphism commutes with D(z), so conjugation fixes it. -/
theorem higgs_adjoint_fixed (z : Circle) (w : Weak) :
    (defining z).comp (higgsEntry w) = (higgsEntry w).comp (defining z) := by
  apply LinearMap.ext; intro x
  change defining z (SU6BoundaryCube.weakIn ((StandardSMGroup.splitEquiv x).2.2 • w)) =
    SU6BoundaryCube.weakIn ((StandardSMGroup.splitEquiv (defining z x)).2.2 • w)
  rw [weak_action,defining_action]
  rfl

/-- Restrict the genuine circle action to fourth roots of unity. -/
def finitePhase : CyclicCharge.Group 4 →* Circle where
  toFun g := ZMod.toCircle (Multiplicative.toAdd g)
  map_one' := by simp
  map_mul' g h := by simp [AddChar.map_add_eq_mul]

theorem finite_quark_phase (g : CyclicCharge.Group 4) :
    (finitePhase g : ℂ)^2 = ZMod.stdAddChar ((2 : ZMod 4)*Multiplicative.toAdd g) := by
  change (ZMod.stdAddChar (Multiplicative.toAdd g))^2 = _
  rw [two_mul,AddChar.map_add_eq_mul,pow_two]

/-- Conjugating a physical right field reverses its residual phase. -/
theorem dual_phase {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ Circle V) (q : ℤ)
    (hr : ∀ z v, r z v = (z : ℂ)^q • v)
    (z : Circle) (f : Module.Dual ℂ V) (v : V) :
    r.dual z f v = (z : ℂ)^(-q) * f v := by
  change f (r z⁻¹ v) = _
  rw [hr,map_smul]
  simp [Circle.coe_inv,zpow_neg]

end
end GUT.SU6BoundaryBaryon
