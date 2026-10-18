import GUT.SU5.Branching.FortySelectedCopies
import Physics.StandardModel.Gauge.SMEpsilonUniqueness
import Mathlib.LinearAlgebra.Multilinear.Basis

namespace GUT.SU5.FortyElectronExclusion
set_option autoImplicit false
noncomputable section
open Math Representation Matter StandardModelEmbedding StandardSMGaugeTensor SMEpsilonTensor
open WedgeKernelProjection FortySelectedCopies FortyHyperchargeExclusion
open scoped TensorProduct
local instance : AddCommGroup Kernel := inferInstance
local instance : Module ℂ Kernel := inferInstance

abbrev F := IntertwiningMap FortySelectedCopies.ambient electronRight

@[simp] theorem C_add (x y : Color) : C (x+y) = C x + C y := map_add colorEmbed x y
@[simp] theorem C_smul (c : ℂ) (x : Color) : C (c • x) = c • C x := map_smul colorEmbed c x

def colorTrilinear (f : F) : Color →ₗ[ℂ] Color →ₗ[ℂ] Color →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun y :=
        { toFun z := f (C x ⊗ₜ[ℂ] pair (C y) (C z))
          map_add' z w := by simp [ pair_add_right, TensorProduct.tmul_add]
          map_smul' c z := by simp [ pair_smul_right, TensorProduct.tmul_smul] }
      map_add' y z := by ext w; simp [ pair_add_left, TensorProduct.tmul_add]
      map_smul' c y := by ext w; simp [ pair_smul_left, TensorProduct.tmul_smul] }
  map_add' x y := by ext z w; simp [ TensorProduct.add_tmul]
  map_smul' c x := by ext z w; simp [ TensorProduct.smul_tmul, TensorProduct.tmul_smul]

theorem C_action (g : GaugeGroup) (x : Color) :
    fundamental (hom g) (C x) = C (downRight g x) :=
  (IntertwiningMap.isIntertwining _ _ colorEmbed g x).symm

theorem colorTrilinear_invariant (f : F)
    (g : Matrix.specialUnitaryGroup (Fin 3) ℂ) (x y z : Color) :
    colorTrilinear f (SmallSpecialUnitary.defining 3 g x)
      (SmallSpecialUnitary.defining 3 g y) (SmallSpecialUnitary.defining 3 g z) =
        colorTrilinear f x y z := by
  let k : GaugeGroup := (g,1,1)
  have hc (v : Color) : downRight k v = SmallSpecialUnitary.defining 3 g v := by
    simp [downRight, twist, color, phase, k, SmallSpecialUnitary.defining]
  have h := IntertwiningMap.isIntertwining _ _ f k (C x ⊗ₜ[ℂ] pair (C y) (C z))
  change f (FortySelectedCopies.ambient k (C x ⊗ₜ[ℂ] pair (C y) (C z))) = _ at h
  have hr := congrArg (fun m : MultilinearMap ℂ (fun _ : Fin 3 => Five)
      (Five ⊗[ℂ] Ten) => m ![C x,C y,C z]) (raw_action (hom k))
  change FortySelectedCopies.ambient k (C x ⊗ₜ[ℂ] pair (C y) (C z)) =
    fundamental (hom k) (C x) ⊗ₜ[ℂ]
      pair (fundamental (hom k) (C y)) (fundamental (hom k) (C z)) at hr
  rw [hr, C_action, C_action, C_action, hc, hc, hc] at h
  change f (C _ ⊗ₜ[ℂ] pair (C _) (C _)) = f (C x ⊗ₜ[ℂ] pair (C y) (C z))
  simp only [electronRight, twist, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.smul_apply, Representation.trivial_apply] at h
  have hp : phase (-6) k = 1 := by simp [phase, k]
  rw [hp, one_smul] at h
  exact h

theorem colorTrilinear_unique (f : F) :
    colorTrilinear f = colorTrilinear f (colorBasis 0) (colorBasis 1) (colorBasis 2) • eps3Trilin :=
  SMEpsilonUniqueness.color_unique (colorTrilinear f) (colorTrilinear_invariant f)

def colorPart : Five →ₗ[ℂ] Color :=
  (LinearMap.fst ℂ Color Weak).comp FundamentalBranching.splitEquiv.toLinearMap
def colorDet : Five [⋀^Fin 3]→ₗ[ℂ] ℂ :=
  (Matrix.detRowAlternating : Color [⋀^Fin 3]→ₗ[ℂ] ℂ).compLinearMap colorPart

theorem colorDet_apply (v : Fin 3 → Five) :
    colorDet v = eps3 (colorPart (v 0)) (colorPart (v 1)) (colorPart (v 2)) := by
  change Matrix.det (fun i => colorPart (v i)) = _
  rw [eps3_det]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem basis_color (i : Fin 3) : fiveBasis (.inl i) = C (colorBasis i) := by
  apply FundamentalBranching.splitEquiv.injective
  simp [fiveBasis, fiveBlockBasis, C, colorBasis, FundamentalBranching.fundamentalEquiv]
theorem basis_weak (i : Fin 2) : fiveBasis (.inr i) = W (weakBasis i) := by
  apply FundamentalBranching.splitEquiv.injective
  simp [fiveBasis, fiveBlockBasis, W, weakBasis, FundamentalBranching.fundamentalEquiv]

theorem basis_raw_action (z : Circle) (i j k : FiveIndex) :
    FortySelectedCopies.ambient (1,1,z)
      (fiveBasis i ⊗ₜ[ℂ] pair (fiveBasis j) (fiveBasis k)) =
    ((z^(fiveWeight i+fiveWeight j+fiveWeight k) : Circle) : ℂ) •
      (fiveBasis i ⊗ₜ[ℂ] pair (fiveBasis j) (fiveBasis k)) := by
  have hr := congrArg (fun m : MultilinearMap ℂ (fun _ : Fin 3 => Five)
      (Five ⊗[ℂ] Ten) => m ![fiveBasis i,fiveBasis j,fiveBasis k]) (raw_action (hom (1,1,z)))
  change FortySelectedCopies.ambient (1,1,z)
    (fiveBasis i ⊗ₜ[ℂ] pair (fiveBasis j) (fiveBasis k)) =
    fundamental (hom (1,1,z)) (fiveBasis i) ⊗ₜ[ℂ]
      pair (fundamental (hom (1,1,z)) (fiveBasis j))
        (fundamental (hom (1,1,z)) (fiveBasis k)) at hr
  rw [hr, five_basis_action, five_basis_action, five_basis_action,
    pair_smul_left, pair_smul_right]
  simp [zpow_add, Circle.coe_mul, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    smul_smul, mul_assoc, mul_comm]

theorem basis_vanish (f : F) (i j k : FiveIndex)
    (hs : fiveWeight i+fiveWeight j+fiveWeight k ∈ ([-1,4,9] : List ℤ)) :
    f (fiveBasis i ⊗ₜ[ℂ] pair (fiveBasis j) (fiveBasis k)) = 0 := by
  have h := IntertwiningMap.isIntertwining _ _ f (1,1,ExoticHyperchargeBasis.root)
    (fiveBasis i ⊗ₜ[ℂ] pair (fiveBasis j) (fiveBasis k))
  rw [basis_raw_action, map_smul, InvariantMassNormalForm.electronRight_hypercharge] at h
  have hn : ((ExoticHyperchargeBasis.root^(fiveWeight i+fiveWeight j+fiveWeight k) : Circle) : ℂ) ≠
      ((ExoticHyperchargeBasis.root^(-6 : ℤ) : Circle) : ℂ) := by
    intro he
    have hc : ((fiveWeight i+fiveWeight j+fiveWeight k : ℤ) : ZMod 31) = (-6 : ZMod 31) := by
      apply ZMod.injective_stdAddChar
      change ((ZMod.toCircle ((fiveWeight i+fiveWeight j+fiveWeight k : ℤ) : ZMod 31) : Circle) : ℂ) = _
      exact ((congrArg (fun z : Circle => (z : ℂ))
        (ExoticHyperchargeBasis.root_zpow (fiveWeight i+fiveWeight j+fiveWeight k))).symm.trans he).trans
        (congrArg (fun z : Circle => (z : ℂ)) (ExoticHyperchargeBasis.root_zpow (-6)))
    have hn : ((fiveWeight i+fiveWeight j+fiveWeight k : ℤ) : ZMod 31) ≠ (-6 : ZMod 31) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with hs | hs | hs <;> simp only [hs] <;> decide
    exact hn hc

  change _ * f _ = _ * f _ at h
  have hz : (((ExoticHyperchargeBasis.root^(fiveWeight i+fiveWeight j+fiveWeight k) : Circle) : ℂ) -
      ((ExoticHyperchargeBasis.root^(-6 : ℤ) : Circle) : ℂ)) * f (fiveBasis i ⊗ₜ[ℂ] pair (fiveBasis j) (fiveBasis k)) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hn)

theorem raw_functional_alternating (f : F) :
    f.toLinearMap.compMultilinearMap raw =
      (colorTrilinear f (colorBasis 0) (colorBasis 1) (colorBasis 2) • colorDet).toMultilinearMap := by
  apply Module.Basis.ext_multilinear (fun _ : Fin 3 => fiveBasis)
  intro v
  have he : (fun i => fiveBasis (v i)) = ![fiveBasis (v 0),fiveBasis (v 1),fiveBasis (v 2)] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  change f (fiveBasis (v 0) ⊗ₜ[ℂ] pair (fiveBasis (v 1)) (fiveBasis (v 2))) =
    colorTrilinear f (colorBasis 0) (colorBasis 1) (colorBasis 2) *
      colorDet ![fiveBasis (v 0),fiveBasis (v 1),fiveBasis (v 2)]
  rw [colorDet_apply]
  rcases v 0 with a | a <;> rcases v 1 with b | b <;> rcases v 2 with c | c
  · rw [basis_color, basis_color, basis_color]
    have h := congrArg (fun t : Color →ₗ[ℂ] Color →ₗ[ℂ] Color →ₗ[ℂ] ℂ =>
      t (colorBasis a) (colorBasis b) (colorBasis c)) (colorTrilinear_unique f)
    change f (C _ ⊗ₜ[ℂ] pair (C _) (C _)) = _ at h
    have hh : eps3Trilin (colorBasis a) (colorBasis b) (colorBasis c) =
        eps3 (colorBasis a) (colorBasis b) (colorBasis c) := rfl
    simpa [colorPart, C, hh] using h
  all_goals
    rw [basis_vanish f _ _ _ (by simp [fiveWeight])]
    simp [colorPart, basis_color, basis_weak, C, W, eps3]

theorem functional_projection_zero (f : F) (v : Five ⊗[ℂ] Ten) : f (projection v) = 0 := by
  let a := colorTrilinear f (colorBasis 0) (colorBasis 1) (colorBasis 2)
  have ht : f.toLinearMap =
      (exteriorPower.alternatingMapLinearEquiv (a • colorDet)).comp ExoticWedgeKernel.wedgeLinear := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    have hr := congrArg (fun m : MultilinearMap ℂ (fun _ : Fin 3 => Five) ℂ =>
      m (Matrix.vecCons x w)) (raw_functional_alternating f)
    change f (x ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 w) =
      exteriorPower.alternatingMapLinearEquiv (a • colorDet)
        (ExoticWedgeKernel.wedgeLinear (x ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 w))
    rw [ExoticWedgeKernel.wedge_tmul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    have hw : ![w 0,w 1] = w := by
      funext i
      fin_cases i <;> rfl
    change f (x ⊗ₜ[ℂ] pair (w 0) (w 1)) = (a • colorDet) (Matrix.vecCons x w) at hr
    rw [pair, hw] at hr
    exact hr
  have hv := LinearMap.congr_fun ht (projection v)
  change f (projection v) =
    exteriorPower.alternatingMapLinearEquiv (a • colorDet)
      (ExoticWedgeKernel.wedgeLinear (projection v)) at hv
  rw [wedge_projection, map_zero] at hv
  exact hv

theorem kernel_electron_zero (f : IntertwiningMap original electronRight) : f = 0 := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro k
  let g : F := f.comp kernelProjection
  have h := functional_projection_zero g (k : Five ⊗[ℂ] Ten)
  rw [projection_on_kernel k] at h
  have hk : kernelProjection (k : Five ⊗[ℂ] Ten) = k := by
    apply Subtype.ext
    exact projection_on_kernel k
  change f (kernelProjection (k : Five ⊗[ℂ] Ten)) = 0 at h
  rw [hk] at h
  change f k = 0
  exact h

theorem electron_hom_zero (f : IntertwiningMap electronRight.dual forty) : f = 0 := by
  let e := SplitRepresentationProjection.bidualEquiv electronRight
  let b := SplitRepresentationProjection.bidualEquiv original
  let t : IntertwiningMap original electronRight :=
    e.symm.toIntertwiningMap.comp ((SplitRepresentationProjection.dualMap f).comp b.toIntertwiningMap)
  have ht := kernel_electron_zero t
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro k
  have hz := congrArg (fun h : IntertwiningMap original electronRight => (e (h k)) phi) ht
  change e (e.symm (SplitRepresentationProjection.dualMap f (b k))) phi = e 0 phi at hz
  rw [Representation.Equiv.apply_symm_apply, map_zero] at hz
  change (f phi) k = 0 at hz
  change (f phi) k = 0
  exact hz

theorem electron_multiplicity_zero :
    Module.finrank ℂ (IntertwiningMap electronRight.dual forty) = 0 := by
  have : Subsingleton (IntertwiningMap electronRight.dual forty) :=
    ⟨fun f g => (electron_hom_zero f).trans (electron_hom_zero g).symm⟩
  exact Module.finrank_zero_of_subsingleton

theorem selected_multiplicity_result :
    0 < Module.finrank ℂ (IntertwiningMap quark forty) ∧
    0 < Module.finrank ℂ (IntertwiningMap upRight.dual forty) ∧
    Module.finrank ℂ (IntertwiningMap electronRight.dual forty) = 0 :=
  ⟨selected_positive_multiplicities.1, selected_positive_multiplicities.2, electron_multiplicity_zero⟩

end
end GUT.SU5.FortyElectronExclusion
