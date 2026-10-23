import GUT.SU5.Representations.WedgeKernelProjection
import GUT.SU5.Branching.FortyHyperchargeExclusion
import Physics.StandardModel.Gauge.Charges.HyperchargeTensorTransport
import Physics.StandardModel.Gauge.Tensors.SMGaugeConjugation

open Physics

namespace GUT.SU5.FortySelectedCopies
set_option autoImplicit false
noncomputable section
open Math Representation Matter StandardModelEmbedding StandardSMGaugeTensor SMEpsilonTensor
open WedgeKernelProjection
open ExoticWedgeKernel (wedgeLinear wedge_tmul)
open scoped TensorProduct

def colorEmbed : IntertwiningMap downRight (fundamental.comp hom) :=
  FundamentalBranching.fundamentalEquiv.symm.toIntertwiningMap.comp
    (IntertwiningMap.inl ℂ downRight (twist weak 3))
def weakEmbed : IntertwiningMap (twist weak 3) (fundamental.comp hom) :=
  FundamentalBranching.fundamentalEquiv.symm.toIntertwiningMap.comp
    (IntertwiningMap.inr ℂ downRight (twist weak 3))
def upEmbed : IntertwiningMap upRight.dual (ten.comp hom) :=
  ExteriorSquareBranching.tenEquiv.symm.toIntertwiningMap.comp
    (IntertwiningMap.inl ℂ upRight.dual (quark.prod electronRight.dual))
def electronEmbed : IntertwiningMap electronRight.dual (ten.comp hom) :=
  ExteriorSquareBranching.tenEquiv.symm.toIntertwiningMap.comp
    ((IntertwiningMap.inr ℂ upRight.dual (quark.prod electronRight.dual)).comp
      (IntertwiningMap.inr ℂ quark electronRight.dual))

abbrev upSource := downRight.tprod electronRight.dual
abbrev quarkSource := (twist weak 3).tprod upRight.dual
abbrev ambient : Representation ℂ GaugeGroup (Five ⊗[ℂ] Ten) :=
  Representation.tprod (fundamental.comp hom) (ten.comp hom)

def upAmbient : IntertwiningMap upSource ambient := colorEmbed.tensor electronEmbed
def quarkAmbient : IntertwiningMap quarkSource ambient := weakEmbed.tensor upEmbed

def kernelProjection : IntertwiningMap ambient FortyHyperchargeExclusion.original where
  toLinearMap :=
    { toFun v := ⟨projection v, wedge_projection v⟩
      map_add' x y := Subtype.ext (map_add projection x y)
      map_smul' c x := Subtype.ext (map_smul projection c x) }
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (projection.isIntertwining' (hom g)) v

def upKernel := kernelProjection.comp upAmbient
def quarkKernel := kernelProjection.comp quarkAmbient

def colorProject : IntertwiningMap (fundamental.comp hom) downRight :=
  (IntertwiningMap.fst ℂ downRight (twist weak 3)).comp
    FundamentalBranching.fundamentalEquiv.toIntertwiningMap
def weakProject : IntertwiningMap (fundamental.comp hom) (twist weak 3) :=
  (IntertwiningMap.snd ℂ downRight (twist weak 3)).comp
    FundamentalBranching.fundamentalEquiv.toIntertwiningMap
def upProject : IntertwiningMap (ten.comp hom) upRight.dual :=
  (IntertwiningMap.fst ℂ upRight.dual (quark.prod electronRight.dual)).comp
    ExteriorSquareBranching.tenEquiv.toIntertwiningMap
def electronProject : IntertwiningMap (ten.comp hom) electronRight.dual :=
  ((IntertwiningMap.snd ℂ quark electronRight.dual).comp
    (IntertwiningMap.snd ℂ upRight.dual (quark.prod electronRight.dual))).comp
    ExteriorSquareBranching.tenEquiv.toIntertwiningMap
def upProbe : IntertwiningMap ambient upSource := colorProject.tensor electronProject
def quarkProbe : IntertwiningMap ambient quarkSource := weakProject.tensor upProject

@[simp] theorem upProbe_tmul (x : Five) (v : Ten) :
    upProbe (x ⊗ₜ[ℂ] v) = (FundamentalBranching.splitEquiv x).1 ⊗ₜ[ℂ]
      (ExteriorSquareBranching.branch v).2.2 := rfl
@[simp] theorem quarkProbe_tmul (x : Five) (v : Ten) :
    quarkProbe (x ⊗ₜ[ℂ] v) = (FundamentalBranching.splitEquiv x).2 ⊗ₜ[ℂ]
      (ExteriorSquareBranching.branch v).1 := rfl

abbrev C (x : Color) : Five := FundamentalBranching.splitEquiv.symm (x,0)
abbrev W (x : Weak) : Five := FundamentalBranching.splitEquiv.symm (0,x)

theorem up_probe_projection (x : Color) (y z : Weak) :
    upProbe (projection (C x ⊗ₜ[ℂ] pair (W y) (W z))) =
      (2/3 : ℂ) • (x ⊗ₜ[ℂ] (eps2 y z • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))) := by
  change upProbe ((C x ⊗ₜ[ℂ] pair (W y) (W z)) -
    sectionLinear (wedgeLinear (C x ⊗ₜ[ℂ] pair (W y) (W z)))) = _
  rw [map_sub]
  simp only [pair, wedge_tmul]
  rw [section_pure]
  simp only [map_smul, map_add, upProbe_tmul]
  simp [pair, ExteriorSquareBranching.branch_wedge,
    ExteriorSquareBranching.pair, C, W]
  module

theorem quark_probe_projection (x : Weak) (y z : Color) :
    quarkProbe (projection (W x ⊗ₜ[ℂ] pair (C y) (C z))) =
      (2/3 : ℂ) • (x ⊗ₜ[ℂ] eps3Trilin y z) := by
  change quarkProbe ((W x ⊗ₜ[ℂ] pair (C y) (C z)) -
    sectionLinear (wedgeLinear (W x ⊗ₜ[ℂ] pair (C y) (C z)))) = _
  rw [map_sub]
  simp only [pair, wedge_tmul]
  rw [section_pure]
  simp only [map_smul, map_add, quarkProbe_tmul]
  simp [pair, ExteriorSquareBranching.branch_wedge,
    ExteriorSquareBranching.pair, C, W]
  module

def upSourceEquiv : Representation.Equiv upSource upRight where
  toLinearEquiv := (TensorProduct.congr (LinearEquiv.refl ℂ Color)
    (HyperchargeTensorTransport.dualLine (-6)).toLinearEquiv).trans
      (TensorProduct.rid ℂ Color)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x phi
    change (electronRight.dual g phi) 1 • (downRight g x) =
      upRight g (phi 1 • x)
    have hp : phase (-2) g * phase 6 g = phase 4 g :=
      (HyperchargeTensorTransport.phase_add (-2) 6 g).symm
    simp only [electronRight, downRight, upRight, twist, MonoidHom.coe_mk,
      OneHom.coe_mk, Representation.dual_apply, Module.Dual.transpose_apply,
      LinearMap.comp_apply, LinearMap.smul_apply, Representation.trivial_apply,
      map_smul]
    rw [HyperchargeTensorTransport.phase_inv]
    change (phase 6 g * phi 1) • (phase (-2) g • color g x) = _
    simp only [smul_smul]
    rw [mul_right_comm (phase 6 g) (phi 1), mul_comm (phase 6 g) (phase (-2) g), hp]
    ring_nf

@[simp] theorem weakDual_apply (w u : Weak) :
    StandardSMContragredient.weakDualLinearEquiv w u = eps2 w u := rfl

def quarkSourceEquiv : Representation.Equiv quarkSource quark.dual where
  toLinearEquiv := (TensorProduct.comm ℂ Weak (Module.Dual ℂ Color)).trans
    ((TensorProduct.congr (LinearEquiv.refl ℂ (Module.Dual ℂ Color))
      StandardSMContragredient.weakDualLinearEquiv).trans
        (TensorProduct.dualDistribEquiv ℂ Color Weak))
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro w phi
    apply TensorProduct.ext'
    intro c u
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      Representation.tprod_apply, TensorProduct.map_tmul,
      TensorProduct.comm_tmul, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, TensorProduct.dualDistribEquiv_tmul_tmul,
      Representation.dual_apply,
      Module.Dual.transpose_apply]
    change eps2 (twist weak 3 g w) u * (upRight.dual g phi) c =
      (TensorProduct.dualDistribEquiv ℂ Color Weak
        (phi ⊗ₜ[ℂ] StandardSMContragredient.weakDualLinearEquiv w))
          (quark g⁻¹ (c ⊗ₜ[ℂ] u))
    have hw := LinearMap.congr_fun
      ((StandardSMContragredient.chargedWeakDualEquiv 3).isIntertwining' g) w
    have hwu := LinearMap.congr_fun hw u
    change eps2 (twist weak 3 g w) u = eps2 w (twist weak (-3) g⁻¹ u) at hwu
    rw [hwu]
    simp only [Representation.dual_apply, Module.Dual.transpose_apply,
      upRight, quark, twist, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply,
      Representation.tprod_apply, TensorProduct.map_tmul,
      map_smul, TensorProduct.dualDistribEquiv_tmul_tmul,
      weakDual_apply, LinearMap.comp_apply,
      HyperchargeTensorTransport.phase_inv, neg_neg]
    simp only [eps2_smul_right, smul_eq_mul]
    have hp : phase (-4) g * phase 3 g = phase (-1) g :=
      (HyperchargeTensorTransport.phase_add (-4) 3 g).symm
    linear_combination hp * phi (color g⁻¹ c) * eps2 w (weak g⁻¹ u)

def kernelInclusion : IntertwiningMap FortyHyperchargeExclusion.original ambient where
  toLinearMap := ExoticWedgeKernel.kernel.toSubmodule.subtype
  isIntertwining' _ := rfl
def upKernelProbe : IntertwiningMap FortyHyperchargeExclusion.original upSource := upProbe.comp kernelInclusion
def quarkKernelProbe : IntertwiningMap FortyHyperchargeExclusion.original quarkSource := quarkProbe.comp kernelInclusion

theorem upKernelProbe_ne_zero : upKernelProbe ≠ 0 := by
  intro h
  let v := C (colorBasis 0) ⊗ₜ[ℂ] pair (W (weakBasis 0)) (W (weakBasis 1))
  let k : FortyHyperchargeExclusion.Kernel := ⟨projection v, wedge_projection v⟩
  have hz := congrArg (fun f : IntertwiningMap FortyHyperchargeExclusion.original upSource => f k) h
  change upProbe (projection v) = 0 at hz
  rw [up_probe_projection] at hz
  let test := TensorProduct.dualDistrib ℂ Color (Module.Dual ℂ ℂ)
    ((Pi.basisFun ℂ (Fin 3)).coord 0 ⊗ₜ[ℂ] Module.Dual.eval ℂ ℂ 1)
  have ht := congrArg test hz
  norm_num [test, TensorProduct.dualDistrib_apply, eps2, weakBasis, colorBasis,
    Module.Basis.coord_apply] at ht

theorem quarkKernelProbe_ne_zero : quarkKernelProbe ≠ 0 := by
  intro h
  let v := W (weakBasis 0) ⊗ₜ[ℂ] pair (C (colorBasis 1)) (C (colorBasis 2))
  let k : FortyHyperchargeExclusion.Kernel := ⟨projection v, wedge_projection v⟩
  have hz := congrArg (fun f : IntertwiningMap FortyHyperchargeExclusion.original quarkSource => f k) h
  change quarkProbe (projection v) = 0 at hz
  rw [quark_probe_projection] at hz
  let test := TensorProduct.dualDistrib ℂ Weak (Module.Dual ℂ Color)
    ((Pi.basisFun ℂ (Fin 2)).coord 0 ⊗ₜ[ℂ] Module.Dual.eval ℂ Color (colorBasis 0))
  have ht := congrArg test hz
  have he : eps3Trilin (colorBasis 1) (colorBasis 2) (colorBasis 0) = 1 := by
    change eps3 (colorBasis 1) (colorBasis 2) (colorBasis 0) = 1
    norm_num [eps3, colorBasis]
  norm_num [test, TensorProduct.dualDistrib_apply, weakBasis,
    Module.Basis.coord_apply, he] at ht

def upCopy : IntertwiningMap upRight.dual FortyHyperchargeExclusion.forty :=
  (SplitRepresentationProjection.dualMap upKernelProbe).comp
    (SplitRepresentationProjection.dualEquiv upSourceEquiv).symm.toIntertwiningMap
def quarkCopy : IntertwiningMap quark FortyHyperchargeExclusion.forty :=
  (SplitRepresentationProjection.dualMap quarkKernelProbe).comp
    ((SplitRepresentationProjection.dualEquiv quarkSourceEquiv).symm.toIntertwiningMap.comp
      (SplitRepresentationProjection.bidualEquiv quark).toIntertwiningMap)

private theorem dualMap_ne_zero {V U : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (r : Representation ℂ GaugeGroup V) (s : Representation ℂ GaugeGroup U)
    (f : IntertwiningMap r s) (hf : f ≠ 0) : SplitRepresentationProjection.dualMap f ≠ 0 := by
  intro h
  apply hf
  apply IntertwiningMap.ext
  apply (Module.dualMap_dualMap_eq_iff ℂ V).mp
  have hd : f.toLinearMap.dualMap = 0 := congrArg IntertwiningMap.toLinearMap h
  have hz : (0 : V →ₗ[ℂ] U).dualMap = 0 := by
    ext phi v
    simp only [LinearMap.dualMap_apply, LinearMap.zero_apply, map_zero]
  rw [hd, IntertwiningMap.zero_toLinearMap, hz]

theorem upCopy_ne_zero : upCopy ≠ 0 := by
  intro h
  apply dualMap_ne_zero (V := FortyHyperchargeExclusion.Kernel)
    (U := Color ⊗[ℂ] Module.Dual ℂ ℂ) FortyHyperchargeExclusion.original
    upSource upKernelProbe upKernelProbe_ne_zero
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro phi
  let e := SplitRepresentationProjection.dualEquiv upSourceEquiv
  have hz := congrArg (fun f : IntertwiningMap upRight.dual FortyHyperchargeExclusion.forty => f (e phi)) h
  change SplitRepresentationProjection.dualMap upKernelProbe (e.symm (e phi)) = 0 at hz
  change SplitRepresentationProjection.dualMap upKernelProbe phi = 0
  simpa only [Representation.Equiv.symm_apply_apply] using hz

theorem quarkCopy_ne_zero : quarkCopy ≠ 0 := by
  intro h
  apply dualMap_ne_zero (V := FortyHyperchargeExclusion.Kernel)
    (U := Weak ⊗[ℂ] Module.Dual ℂ Color) FortyHyperchargeExclusion.original
    quarkSource quarkKernelProbe quarkKernelProbe_ne_zero
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro phi
  let e := (SplitRepresentationProjection.bidualEquiv quark).trans
    (SplitRepresentationProjection.dualEquiv quarkSourceEquiv).symm
  have hz := congrArg (fun f : IntertwiningMap quark FortyHyperchargeExclusion.forty => f (e.symm phi)) h
  change SplitRepresentationProjection.dualMap quarkKernelProbe (e (e.symm phi)) = 0 at hz
  change SplitRepresentationProjection.dualMap quarkKernelProbe phi = 0
  simpa only [Representation.Equiv.apply_symm_apply] using hz

theorem selected_positive_multiplicities :
    0 < Module.finrank ℂ (IntertwiningMap quark FortyHyperchargeExclusion.forty) ∧
    0 < Module.finrank ℂ (IntertwiningMap upRight.dual FortyHyperchargeExclusion.forty) :=
  ⟨Module.finrank_pos_iff_exists_ne_zero.mpr ⟨quarkCopy, quarkCopy_ne_zero⟩,
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨upCopy, upCopy_ne_zero⟩⟩

end
end GUT.SU5.FortySelectedCopies
