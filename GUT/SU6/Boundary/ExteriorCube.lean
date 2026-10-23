import GUT.SU6.Adapters.StandardSMExterior
import Math.LinearAlgebra.Exterior.ExteriorCubeHook

/-! A split, SM-equivariant copy of the right up-quark in the actual exterior
cube of the defining SU(6) representation. No bulk mode equation is assumed. -/
namespace GUT.SU6BoundaryCube
set_option autoImplicit false
noncomputable section
open Math Physics StandardSMGaugeTensor SMEpsilonTensor StandardSMExterior
open scoped TensorProduct

abbrev Vector := Fin 6 → ℂ
abbrev Cube := ⋀[ℂ]^3 Vector
abbrev Square := ⋀[ℂ]^2 Vector

def colorIn : Color →ₗ[ℂ] Vector :=
  StandardSMGroup.splitEquiv.symm.toLinearMap.comp (LinearMap.inl ℂ Color (Weak × ℂ))
def weakIn : Weak →ₗ[ℂ] Vector :=
  StandardSMGroup.splitEquiv.symm.toLinearMap.comp
    ((LinearMap.inr ℂ Color (Weak × ℂ)).comp (LinearMap.inl ℂ Weak ℂ))
def colorOut : Vector →ₗ[ℂ] Color :=
  (LinearMap.fst ℂ Color (Weak × ℂ)).comp StandardSMGroup.splitEquiv.toLinearMap

def area : Square →ₗ[ℂ] ℂ where
  toFun x := (StandardSMExterior.branch x).2.2.1 1
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def volume : Square := StandardSMExterior.wedge (0, (weakBasis 0, 0)) (0, (weakBasis 1, 0))

def embed : Color →ₗ[ℂ] Cube :=
  (ExteriorCubeHook.multiply.comp
    ((TensorProduct.mk ℂ Vector Square).flip volume)).comp colorIn

def contract : Cube →ₗ[ℂ] Color :=
  ((TensorProduct.rid ℂ Color).toLinearMap.comp
    (TensorProduct.map colorOut area)).comp ExteriorCubeHook.coproduct

@[simp] theorem area_wedge (a b : Vector) :
    area (exteriorPower.ιMulti ℂ 2 ![a,b]) =
      eps2 (StandardSMGroup.splitEquiv a).2.1 (StandardSMGroup.splitEquiv b).2.1 := by
  simp [area, StandardSMExterior.branch_wedge, StandardSMExterior.pair]

theorem embed_cube (x : Color) :
    embed x = ExteriorCubeHook.cube (colorIn x) (weakIn (weakBasis 0)) (weakIn (weakBasis 1)) := by
  change ExteriorCubeHook.multiply (colorIn x ⊗ₜ[ℂ] volume) = _
  exact ExteriorCubeHook.multiply_pure _ _ _

@[simp] theorem contract_cube (a b c : Vector) :
    contract (ExteriorCubeHook.cube a b c) =
      eps2 (StandardSMGroup.splitEquiv b).2.1 (StandardSMGroup.splitEquiv c).2.1 • colorOut a -
      eps2 (StandardSMGroup.splitEquiv a).2.1 (StandardSMGroup.splitEquiv c).2.1 • colorOut b +
      eps2 (StandardSMGroup.splitEquiv a).2.1 (StandardSMGroup.splitEquiv b).2.1 • colorOut c := by
  simp [contract, ExteriorCubeHook.coproduct_pure,
    Math.ExteriorSquareTensorDescent.wedge_tmul, TensorProduct.map_tmul]

@[simp] theorem contract_embed (x : Color) : contract (embed x) = x := by
  rw [embed_cube, contract_cube]
  simp [colorIn, weakIn, colorOut, eps2_basis]

theorem embed_injective : Function.Injective embed :=
  Function.LeftInverse.injective contract_embed

private theorem phase_product (g : GaugeGroup) : phase 6 g * phase (-2) g = phase 4 g := by
  change (↑(g.2.2 ^ (6 : ℤ)) : ℂ) * ↑(g.2.2 ^ (-2 : ℤ)) = ↑(g.2.2 ^ (4 : ℤ))
  rw [← Circle.coe_mul, ← zpow_add]
  rfl

private theorem area_covariant (g : GaugeGroup) (x : Square) :
    area (exteriorPower.map 2 (FundamentalRepresentation.rho (StandardSMGroup.hom g)) x) =
      phase 6 g * area x := by
  have he := Representation.IntertwiningMap.isIntertwining _ _
    StandardSMExterior.branchIntertwiner g x
  have h := congrArg (fun b : StandardSMExterior.Blocks => b.2.2.1 1) he
  change area (exteriorPower.map 2 (FundamentalRepresentation.rho (StandardSMGroup.hom g)) x) =
    (electronRight.dual g (StandardSMExterior.branch x).2.2.1) 1 at h
  rw [h]
  change (StandardSMExterior.branch x).2.2.1 (electronRight g⁻¹ 1) = _
  have hg : electronRight g⁻¹ 1 = phase 6 g := by
    simp [electronRight, twist, phase]
  rw [hg]
  simpa only [smul_eq_mul, mul_one, area, LinearMap.coe_mk, AddHom.coe_mk] using
    ((StandardSMExterior.branch x).2.2.1.map_smul (phase 6 g) (1 : ℂ))

theorem volume_branch : StandardSMExterior.branch volume =
    (0, (0, (LinearMap.id, (0,0)))) := by
  simp [volume, StandardSMExterior.wedge, StandardSMExterior.pair, eps2_basis, eps3Trilin]

theorem volume_covariant (g : GaugeGroup) :
    exteriorPower.map 2 (FundamentalRepresentation.rho (StandardSMGroup.hom g)) volume =
      phase 6 g • volume := by
  apply StandardSMExterior.branch_bijective.1
  rw [map_smul]
  have he := Representation.IntertwiningMap.isIntertwining _ _
    StandardSMExterior.branchIntertwiner g volume
  change StandardSMExterior.branch
      (exteriorPower.map 2 (FundamentalRepresentation.rho (StandardSMGroup.hom g)) volume) =
    StandardSMExterior.blocksRho g (StandardSMExterior.branch volume) at he
  rw [he, volume_branch]
  ext <;> simp [StandardSMExterior.blocksRho, electronRight, twist, phase]
  change (Circle.coeHom g.2.2)^6 * ((Representation.trivial ℂ GaugeGroup ℂ) g⁻¹ 1) = _
  simp

theorem colorIn_covariant (g : GaugeGroup) (x : Color) :
    FundamentalRepresentation.rho (StandardSMGroup.hom g) (colorIn x) =
      colorIn (twist color (-2) g x) := by
  apply StandardSMGroup.splitEquiv.injective
  rw [StandardSMGroup.splitEquiv_action]
  simp [colorIn, StandardSMGroup.heavy]

theorem embed_covariant (g : GaugeGroup) (x : Color) :
    exteriorPower.map 3 (FundamentalRepresentation.rho (StandardSMGroup.hom g)) (embed x) =
      embed (upRight g x) := by
  change exteriorPower.map 3 _ (ExteriorCubeHook.multiply (colorIn x ⊗ₜ[ℂ] volume)) = _
  rw [← ExteriorCubeHook.multiply_natural, colorIn_covariant, volume_covariant,
    TensorProduct.tmul_smul, map_smul]
  change phase 6 g • embed (twist color (-2) g x) = _
  rw [← map_smul]
  congr 1
  simp [upRight, twist, smul_smul, phase_product]

private theorem colorOut_covariant (g : GaugeGroup) (x : Vector) :
    colorOut (FundamentalRepresentation.rho (StandardSMGroup.hom g) x) =
      twist color (-2) g (colorOut x) := by
  exact congrArg Prod.fst (StandardSMGroup.splitEquiv_action g x)

theorem contract_covariant (g : GaugeGroup) (x : Cube) :
    contract (exteriorPower.map 3 (FundamentalRepresentation.rho (StandardSMGroup.hom g)) x) =
      upRight g (contract x) := by
  let f := FundamentalRepresentation.rho (StandardSMGroup.hom g)
  have ht : ((TensorProduct.rid ℂ Color).toLinearMap.comp (TensorProduct.map colorOut area)).comp
      (TensorProduct.map f (exteriorPower.map 2 f)) =
      (upRight g).comp ((TensorProduct.rid ℂ Color).toLinearMap.comp
        (TensorProduct.map colorOut area)) := by
    apply TensorProduct.ext'
    intro a b
    change area (exteriorPower.map 2 f b) • colorOut (f a) = upRight g (area b • colorOut a)
    rw [area_covariant, colorOut_covariant, map_smul]
    change (phase 6 g * area b) • (phase (-2) g • color g (colorOut a)) =
      area b • (phase 4 g • color g (colorOut a))
    rw [smul_smul, smul_smul]
    have hp := phase_product g
    congr 1
    calc
      (phase 6 g * area b) * phase (-2) g = (phase 6 g * phase (-2) g) * area b := by ring
      _ = area b * phase 4 g := by rw [hp, mul_comm]
  change ((TensorProduct.rid ℂ Color).toLinearMap.comp (TensorProduct.map colorOut area))
    (ExteriorCubeHook.coproduct (exteriorPower.map 3 f x)) = _
  rw [ExteriorCubeHook.coproduct_natural]
  exact LinearMap.congr_fun ht (ExteriorCubeHook.coproduct x)

end
end GUT.SU6BoundaryCube
