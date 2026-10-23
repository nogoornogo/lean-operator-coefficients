import GUT.SU5.SelectionRules.MatrixTenMass
import Physics.FieldTheory.Mass.Algebra.BipartiteNormalForm
import Physics.StandardModel.Gauge.Tensors.StandardSMIrreducibility
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Math.RepresentationTheory.Decomposition.Schur
import Physics.StandardModel.Operators.BaryonOne.Qque.PhysicalQqueEndpoint

open Physics

/-! Actual SU(5) matter forbids same-side mass blocks under SM invariance.
An arbitrary invariant symmetric mass therefore has a derived Dirac form. -/
-- Elaborate proofs sequentially to avoid blocked worker stacks.
set_option Elab.async false

namespace GUT.SU5.InvariantMassNormalForm
set_option autoImplicit false
noncomputable section
open Math Representation StandardModelEmbedding Matter StandardSMGaugeTensor SMEpsilonTensor
open BipartiteNormalForm
local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup Ten := inferInstance

def HasHypercharge {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ GaugeGroup V) (y : ℤ) : Prop :=
  ∀ (z : Circle) (v : V), rho (1, 1, z) v = ((z ^ y : Circle) : ℂ) • v

theorem hypercharge_dual {V : Type*} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ GaugeGroup V} {y : ℤ}
    (hy : HasHypercharge rho y) : HasHypercharge rho.dual (-y) := by
  intro z f
  ext v
  change f (rho (1, 1, z)⁻¹ v) = (((z ^ (-y) : Circle) : ℂ) • f) v
  simp only [Prod.inv_mk, inv_one]
  rw [hy z⁻¹ v, map_smul]
  simp only [LinearMap.smul_apply, inv_zpow, zpow_neg]

@[simp] private theorem coeHom_apply (z : Circle) : Circle.coeHom z = (z : ℂ) := rfl

theorem quark_hypercharge : HasHypercharge quark 1 := by
  intro z v
  simp [quark, twist, phase, color, weak, Representation.tprod_apply]

theorem upRight_hypercharge : HasHypercharge upRight 4 := by
  intro z v
  simp [upRight, twist, phase, color]

theorem downRight_hypercharge : HasHypercharge downRight (-2) := by
  intro z v
  simp [downRight, twist, phase, color]

theorem lepton_hypercharge : HasHypercharge lepton (-3) := by
  intro z v
  simp [lepton, twist, phase, weak]

theorem electronRight_hypercharge : HasHypercharge electronRight (-6) := by
  intro z v
  simp [electronRight, twist, phase, Representation.trivial]

theorem trivial_hypercharge (V : Type*) [AddCommGroup V] [Module ℂ V] :
    HasHypercharge (Representation.trivial ℂ GaugeGroup V) 0 := by
  intro z v
  simp [Representation.trivial]

theorem upLeft_hypercharge : HasHypercharge upRight.dual (-4) :=
  hypercharge_dual upRight_hypercharge
theorem downLeft_hypercharge : HasHypercharge downRight.dual 2 :=
  hypercharge_dual downRight_hypercharge
theorem electronLeft_hypercharge : HasHypercharge electronRight.dual 6 :=
  hypercharge_dual electronRight_hypercharge

/-- A bounded phase probe suffices for the actual SM charges. No circle
homomorphism classification or historical SU6 lattice module is used. -/
theorem bounded_weights_separated (a b : ℤ)
    (ha : -6 ≤ a ∧ a ≤ 6) (hb : -6 ≤ b ∧ b ≤ 6) (hn : a ≠ b) :
    ∃ z : Circle, ((z ^ a : Circle) : ℂ) ≠ ((z ^ b : Circle) : ℂ) := by
  let d : ℝ := Real.pi / 16
  have hd : 0 < d := div_pos Real.pi_pos (by norm_num)
  have hbound (c : ℤ) (hc : -6 ≤ c ∧ c ≤ 6) :
      (c : ℝ) * d ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2) := by
    have hlo : (-6 : ℝ) ≤ c := by exact_mod_cast hc.1
    have hhi : (c : ℝ) ≤ 6 := by exact_mod_cast hc.2
    have h1 := mul_le_mul_of_nonneg_right hlo hd.le
    have h2 := mul_le_mul_of_nonneg_right hhi hd.le
    dsimp [d] at h1 h2 ⊢
    constructor <;> nlinarith [Real.pi_pos]
  refine ⟨Circle.exp d, ?_⟩
  intro he
  have he' : Circle.exp d ^ a = Circle.exp d ^ b := Subtype.coe_injective he
  rw [← Circle.exp_intCast_mul, ← Circle.exp_intCast_mul] at he'
  have hangle := Circle.exp_injOn_Icc
    (a := -Real.pi / 2) (b := Real.pi / 2) (by linarith [Real.pi_pos])
    (hbound a ha) (hbound b hb) he'
  have hab : (a : ℝ) = (b : ℝ) := mul_right_cancel₀ (ne_of_gt hd) hangle
  exact hn (by exact_mod_cast hab)

theorem no_pair_of_weights {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {r : Representation ℂ GaugeGroup V}
    {s : Representation ℂ GaugeGroup W} {a b : ℤ}
    (hr : HasHypercharge r a) (hs : HasHypercharge s b) (h : a ≠ -b)
    (ha : -6 ≤ a ∧ a ≤ 6 := by norm_num)
    (hb : -6 ≤ b ∧ b ≤ 6 := by norm_num) : NoPairings r s := by
  obtain ⟨z,hz⟩ := bounded_weights_separated a (-b) ha (by omega) h
  intro f
  exact FiniteSpectrum.intertwiner_eq_zero_of_scalar r s.dual (1,1,z) _ _
    (hr z) ((hypercharge_dual hs) z) hz f

theorem blocks_ten_ten : NoPairings ((upRight.dual).prod ((quark).prod (electronRight.dual))) ((upRight.dual).prod ((quark).prod (electronRight.dual))) :=
  prod_left (prod_right (no_pair_of_weights (upLeft_hypercharge) (upLeft_hypercharge) (by norm_num)) (prod_right (no_pair_of_weights (upLeft_hypercharge) (quark_hypercharge) (by norm_num)) (no_pair_of_weights (upLeft_hypercharge) (electronLeft_hypercharge) (by norm_num)))) (prod_left (prod_right (no_pair_of_weights (quark_hypercharge) (upLeft_hypercharge) (by norm_num)) (prod_right (no_pair_of_weights (quark_hypercharge) (quark_hypercharge) (by norm_num)) (no_pair_of_weights (quark_hypercharge) (electronLeft_hypercharge) (by norm_num)))) (prod_right (no_pair_of_weights (electronLeft_hypercharge) (upLeft_hypercharge) (by norm_num)) (prod_right (no_pair_of_weights (electronLeft_hypercharge) (quark_hypercharge) (by norm_num)) (no_pair_of_weights (electronLeft_hypercharge) (electronLeft_hypercharge) (by norm_num)))))

theorem blocks_ten_bar : NoPairings ((upRight.dual).prod ((quark).prod (electronRight.dual))) ((downRight.dual).prod (lepton)) :=
  prod_left (prod_right (no_pair_of_weights (upLeft_hypercharge) (downLeft_hypercharge) (by norm_num)) (no_pair_of_weights (upLeft_hypercharge) (lepton_hypercharge) (by norm_num))) (prod_left (prod_right (no_pair_of_weights (quark_hypercharge) (downLeft_hypercharge) (by norm_num)) (no_pair_of_weights (quark_hypercharge) (lepton_hypercharge) (by norm_num))) (prod_right (no_pair_of_weights (electronLeft_hypercharge) (downLeft_hypercharge) (by norm_num)) (no_pair_of_weights (electronLeft_hypercharge) (lepton_hypercharge) (by norm_num))))

theorem blocks_bar_ten : NoPairings ((downRight.dual).prod (lepton)) ((upRight.dual).prod ((quark).prod (electronRight.dual))) :=
  prod_left (prod_right (no_pair_of_weights (downLeft_hypercharge) (upLeft_hypercharge) (by norm_num)) (prod_right (no_pair_of_weights (downLeft_hypercharge) (quark_hypercharge) (by norm_num)) (no_pair_of_weights (downLeft_hypercharge) (electronLeft_hypercharge) (by norm_num)))) (prod_right (no_pair_of_weights (lepton_hypercharge) (upLeft_hypercharge) (by norm_num)) (prod_right (no_pair_of_weights (lepton_hypercharge) (quark_hypercharge) (by norm_num)) (no_pair_of_weights (lepton_hypercharge) (electronLeft_hypercharge) (by norm_num))))

theorem blocks_bar_bar : NoPairings ((downRight.dual).prod (lepton)) ((downRight.dual).prod (lepton)) :=
  prod_left (prod_right (no_pair_of_weights (downLeft_hypercharge) (downLeft_hypercharge) (by norm_num)) (no_pair_of_weights (downLeft_hypercharge) (lepton_hypercharge) (by norm_num))) (prod_right (no_pair_of_weights (lepton_hypercharge) (downLeft_hypercharge) (by norm_num)) (no_pair_of_weights (lepton_hypercharge) (lepton_hypercharge) (by norm_num)))

theorem blocks_dual_ten_dual_ten : NoPairings ((upRight.dual.dual).prod ((quark.dual).prod (electronRight.dual.dual))) ((upRight.dual.dual).prod ((quark.dual).prod (electronRight.dual.dual))) :=
  prod_left (prod_right (no_pair_of_weights (hypercharge_dual upLeft_hypercharge) (hypercharge_dual upLeft_hypercharge) (by norm_num)) (prod_right (no_pair_of_weights (hypercharge_dual upLeft_hypercharge) (hypercharge_dual quark_hypercharge) (by norm_num)) (no_pair_of_weights (hypercharge_dual upLeft_hypercharge) (hypercharge_dual electronLeft_hypercharge) (by norm_num)))) (prod_left (prod_right (no_pair_of_weights (hypercharge_dual quark_hypercharge) (hypercharge_dual upLeft_hypercharge) (by norm_num)) (prod_right (no_pair_of_weights (hypercharge_dual quark_hypercharge) (hypercharge_dual quark_hypercharge) (by norm_num)) (no_pair_of_weights (hypercharge_dual quark_hypercharge) (hypercharge_dual electronLeft_hypercharge) (by norm_num)))) (prod_right (no_pair_of_weights (hypercharge_dual electronLeft_hypercharge) (hypercharge_dual upLeft_hypercharge) (by norm_num)) (prod_right (no_pair_of_weights (hypercharge_dual electronLeft_hypercharge) (hypercharge_dual quark_hypercharge) (by norm_num)) (no_pair_of_weights (hypercharge_dual electronLeft_hypercharge) (hypercharge_dual electronLeft_hypercharge) (by norm_num)))))


def dualTenBlocksEquiv : Equiv (Representation.dual (ten.comp hom))
    (upRight.dual.dual.prod (quark.dual.prod electronRight.dual.dual)) :=
  (SplitRepresentationProjection.dualEquiv ExteriorSquareBranching.tenEquiv).trans
    ((SplitRepresentationProjection.dualProdEquiv upRight.dual
      (quark.prod electronRight.dual)).symm.trans
      (SplitRepresentationProjection.prodEquiv (Representation.Equiv.refl _)
        (SplitRepresentationProjection.dualProdEquiv quark electronRight.dual).symm))

theorem ten_ten : NoPairings (ten.comp hom) (ten.comp hom) :=
  BipartiteNormalForm.equiv ExteriorSquareBranching.tenEquiv
    ExteriorSquareBranching.tenEquiv blocks_ten_ten

theorem ten_bar : NoPairings (ten.comp hom) (antifundamental.comp hom) :=
  BipartiteNormalForm.equiv ExteriorSquareBranching.tenEquiv
    FundamentalBranching.antifundamentalEquiv blocks_ten_bar

theorem bar_ten : NoPairings (antifundamental.comp hom) (ten.comp hom) :=
  BipartiteNormalForm.equiv FundamentalBranching.antifundamentalEquiv
    ExteriorSquareBranching.tenEquiv blocks_bar_ten

theorem bar_bar : NoPairings (antifundamental.comp hom) (antifundamental.comp hom) :=
  BipartiteNormalForm.equiv FundamentalBranching.antifundamentalEquiv
    FundamentalBranching.antifundamentalEquiv blocks_bar_bar

theorem dual_ten_dual_ten : NoPairings (Representation.dual (ten.comp hom)) (Representation.dual (ten.comp hom)) :=
  BipartiteNormalForm.equiv dualTenBlocksEquiv dualTenBlocksEquiv blocks_dual_ten_dual_ten


def upI := IntertwiningMap.inl ℂ upRight.dual (quark.prod electronRight.dual)
def quarkI := (IntertwiningMap.inr ℂ upRight.dual (quark.prod electronRight.dual)).comp
  (IntertwiningMap.inl ℂ quark electronRight.dual)
def electronI := (IntertwiningMap.inr ℂ upRight.dual (quark.prod electronRight.dual)).comp
  (IntertwiningMap.inr ℂ quark electronRight.dual)
def upP := IntertwiningMap.fst ℂ upRight.dual (quark.prod electronRight.dual)
def quarkP := (IntertwiningMap.fst ℂ quark electronRight.dual).comp
  (IntertwiningMap.snd ℂ upRight.dual (quark.prod electronRight.dual))
def electronP := (IntertwiningMap.snd ℂ quark electronRight.dual).comp
  (IntertwiningMap.snd ℂ upRight.dual (quark.prod electronRight.dual))

theorem blocks_endomorphism (F : IntertwiningMap ExteriorSquareBranching.blocksRho
    ExteriorSquareBranching.blocksRho) :
    ∃ r : MixedTenMass.RowWeights, F = MixedTenMass.weightedBlocks r := by
  let : IsIrreducible upRight.dual := StandardSMIrreducibility.upLeft_irreducible
  let : IsIrreducible quark := StandardSMIrreducibility.quark_irreducible
  let : IsIrreducible electronRight.dual := StandardSMIrreducibility.electronLeft_irreducible
  obtain ⟨upC, hup⟩ := BlockCentralizer.intertwiningMap_eq_smul_one_of_irreducible _
    (upP.comp (F.comp upI))
  obtain ⟨quarkC, hquark⟩ := BlockCentralizer.intertwiningMap_eq_smul_one_of_irreducible _
    (quarkP.comp (F.comp quarkI))
  obtain ⟨electronC, helectron⟩ := BlockCentralizer.intertwiningMap_eq_smul_one_of_irreducible _
    (electronP.comp (F.comp electronI))
  have hupquark := BlockCentralizer.intertwiningMap_eq_zero_of_finrank_ne
    (by simp [Quark, Color, Weak, Module.finrank_tensorProduct]) (upP.comp (F.comp quarkI))
  have hupelectron := BlockCentralizer.intertwiningMap_eq_zero_of_finrank_ne
    (by simp [Color]) (upP.comp (F.comp electronI))
  have hquarkup := BlockCentralizer.intertwiningMap_eq_zero_of_finrank_ne
    (by simp [Quark, Color, Weak, Module.finrank_tensorProduct]) (quarkP.comp (F.comp upI))
  have hquarkelectron := BlockCentralizer.intertwiningMap_eq_zero_of_finrank_ne
    (by simp [Quark, Color, Weak, Module.finrank_tensorProduct]) (quarkP.comp (F.comp electronI))
  have helectronup := BlockCentralizer.intertwiningMap_eq_zero_of_finrank_ne
    (by simp [Color]) (electronP.comp (F.comp upI))
  have helectronquark := BlockCentralizer.intertwiningMap_eq_zero_of_finrank_ne
    (by simp [Quark, Color, Weak, Module.finrank_tensorProduct]) (electronP.comp (F.comp quarkI))
  refine ⟨⟨upC, quarkC, electronC⟩, ?_⟩
  apply DFunLike.ext
  rintro ⟨u,q,e⟩
  have hd : (u,(q,e)) = upI u + quarkI q + electronI e := by
    change (u,(q,e)) = (u,0) + (0,(q,0)) + (0,(0,e))
    simp
  apply Prod.ext
  · change (F (u,(q,e))).1 = upC • u
    rw [hd, map_add, map_add]
    simp only [Prod.fst_add]
    have hupv := DFunLike.congr_fun hup u
    change (F (upI u)).1 = upC • u at hupv
    have hquarkv := DFunLike.congr_fun hupquark q
    change (F (quarkI q)).1 = 0 at hquarkv
    have helectronv := DFunLike.congr_fun hupelectron e
    change (F (electronI e)).1 = 0 at helectronv
    simp [hupv, hquarkv, helectronv]
  · apply Prod.ext
    · change (F (u,(q,e))).2.1 = quarkC • q
      rw [hd, map_add, map_add]
      simp only [Prod.fst_add, Prod.snd_add]
      have hupv := DFunLike.congr_fun hquarkup u
      change (F (upI u)).2.1 = 0 at hupv
      have hquarkv := DFunLike.congr_fun hquark q
      change (F (quarkI q)).2.1 = quarkC • q at hquarkv
      have helectronv := DFunLike.congr_fun hquarkelectron e
      change (F (electronI e)).2.1 = 0 at helectronv
      simp [hupv, hquarkv, helectronv]
    · change (F (u,(q,e))).2.2 = electronC • e
      rw [hd, map_add, map_add]
      simp only [Prod.snd_add]
      have hupv := DFunLike.congr_fun helectronup u
      change (F (upI u)).2.2 = 0 at hupv
      have hquarkv := DFunLike.congr_fun helectronquark q
      change (F (quarkI q)).2.2 = 0 at hquarkv
      have helectronv := DFunLike.congr_fun helectron e
      change (F (electronI e)).2.2 = electronC • e at helectronv
      simp [hupv, hquarkv, helectronv]

theorem ten_endomorphism (F : IntertwiningMap (ten.comp hom) (ten.comp hom)) :
    ∃ r : MixedTenMass.RowWeights, F = MixedTenMass.weighted r := by
  let E := ExteriorSquareBranching.tenEquiv
  obtain ⟨r,hr⟩ := blocks_endomorphism (E.toIntertwiningMap.comp (F.comp E.symm.toIntertwiningMap))
  refine ⟨r, ?_⟩
  apply DFunLike.ext
  intro x
  have he := DFunLike.congr_fun hr (E x)
  have he' : E (F x) = MixedTenMass.weightedBlocks r (E x) := by simpa using he
  apply E.injective
  change E.toLinearEquiv (F x) = E.toLinearEquiv
    (E.toLinearEquiv.symm (MixedTenMass.weightedBlocks r (E x)))
  rw [E.toLinearEquiv.apply_symm_apply]
  exact he'


theorem bar_dual_ten : NoPairings (antifundamental.comp hom) (Representation.dual (ten.comp hom)) :=
  BipartiteNormalForm.equiv FundamentalBranching.antifundamentalEquiv dualTenBlocksEquiv
    (prod_left
      (prod_right (no_pair_of_weights downLeft_hypercharge (hypercharge_dual upLeft_hypercharge) (by norm_num))
        (prod_right (no_pair_of_weights downLeft_hypercharge (hypercharge_dual quark_hypercharge) (by norm_num))
          (no_pair_of_weights downLeft_hypercharge (hypercharge_dual electronLeft_hypercharge) (by norm_num))))
      (prod_right (no_pair_of_weights lepton_hypercharge (hypercharge_dual upLeft_hypercharge) (by norm_num))
        (prod_right (no_pair_of_weights lepton_hypercharge (hypercharge_dual quark_hypercharge) (by norm_num))
          (no_pair_of_weights lepton_hypercharge (hypercharge_dual electronLeft_hypercharge) (by norm_num)))))

theorem bar_to_ten_zero (F : IntertwiningMap (antifundamental.comp hom) (ten.comp hom)) : F = 0 := by
  have hz := bar_dual_ten ((SplitRepresentationProjection.bidualEquiv (ten.comp hom)).toIntertwiningMap.comp F)
  apply DFunLike.ext
  intro x
  apply (SplitRepresentationProjection.bidualEquiv (ten.comp hom)).injective
  simpa using DFunLike.congr_fun hz x

def sourceSM (p : ℕ) := (FiniteSpectrum.copies p (ten.comp hom)).prod
  (antifundamental.comp hom)
def targetSM (q : ℕ) := FiniteSpectrum.copies q (ten.comp hom)

theorem source_no_pairings (p : ℕ) : NoPairings (sourceSM p) (sourceSM p) :=
  prod_left (prod_right (copies_right (copies_left ten_ten p) p) (copies_left ten_bar p))
    (prod_right (copies_right bar_ten p) bar_bar)

theorem target_dual_no_pairings (q : ℕ) : NoPairings (targetSM q).dual (targetSM q).dual :=
  BipartiteNormalForm.equiv (dualCopiesEquiv q (ten.comp hom))
    (dualCopiesEquiv q (ten.comp hom))
    (copies_right (copies_left dual_ten_dual_ten q) q)

variable {H : Type*} [CommGroup H] (chi psi : H →* Circle)

private def gaugeInclusion : GaugeGroup →* GaugeGroup × H := MonoidHom.inl _ _

theorem source_restriction (p : ℕ) :
    (MatrixTenMass.sourceRho chi psi p).comp gaugeInclusion = sourceSM p := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  rintro ⟨x,y⟩
  apply Prod.ext
  · funext i
    change (chi 1 : ℂ) • ten (hom g) (x i) = ten (hom g) (x i)
    simp
  · change (psi 1 : ℂ) • antifundamental (hom g) y = antifundamental (hom g) y
    simp

theorem target_restriction (q : ℕ) :
    (MatrixTenMass.targetRho chi q).comp gaugeInclusion = targetSM q := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  funext i
  change (chi 1 : ℂ) • ten (hom g) (x i) = ten (hom g) (x i)
  simp

theorem source_joint_no_pairings (p : ℕ) :
    NoPairings (MatrixTenMass.sourceRho chi psi p) (MatrixTenMass.sourceRho chi psi p) := by
  apply of_comp gaugeInclusion
  rw [source_restriction]
  exact source_no_pairings p

theorem target_joint_dual_no_pairings (q : ℕ) :
    NoPairings (MatrixTenMass.targetRho chi q).dual (MatrixTenMass.targetRho chi q).dual := by
  apply of_comp gaugeInclusion
  rw [SplitRepresentationProjection.dual_comp, target_restriction]
  exact target_dual_no_pairings q

theorem normal_form (p q : ℕ)
    (B : InvariantWeylMass.SymmetricMass (MatrixTenMass.fieldsRho chi psi p q)) :
    B.form = (InvariantWeylMass.ofDirac
      (crossMap (MatrixTenMass.sourceRho chi psi p) (MatrixTenMass.targetRho chi q) B)).form :=
  BipartiteNormalForm.normal_form _ _ B
    (source_joint_no_pairings chi psi p) (target_joint_dual_no_pairings chi q)

variable {p q : ℕ}

def restrictMassMap (M : IntertwiningMap (MatrixTenMass.sourceRho chi psi p)
    (MatrixTenMass.targetRho chi q)) : IntertwiningMap (sourceSM p) (targetSM q) where
  toLinearMap := M.toLinearMap
  isIntertwining' g := by
    have he := M.isIntertwining' (g,1)
    have es := congrArg (fun R : Representation ℂ GaugeGroup (MatrixTenMass.Source p) => R g)
      (source_restriction chi psi p)
    have et := congrArg (fun R : Representation ℂ GaugeGroup (MatrixTenMass.Target q) => R g)
      (target_restriction chi q)
    change MatrixTenMass.sourceRho chi psi p (g,1) = sourceSM p g at es
    change MatrixTenMass.targetRho chi q (g,1) = targetSM q g at et
    rw [es,et] at he
    exact he

def entry (M : IntertwiningMap (sourceSM p) (targetSM q)) (j : Fin q) (i : Fin p) :=
  ((FiniteSpectrum.homCopies q (sourceSM p) (ten.comp hom) M) j).comp
    ((IntertwiningMap.inl ℂ (FiniteSpectrum.copies p (ten.comp hom))
      (antifundamental.comp hom)).comp (copySlot p (ten.comp hom) i))

def rows (M : IntertwiningMap (sourceSM p) (targetSM q)) (j : Fin q) (i : Fin p) :=
  Classical.choose (ten_endomorphism (entry M j i))

theorem rows_spec (M : IntertwiningMap (sourceSM p) (targetSM q)) (j : Fin q) (i : Fin p) :
    entry M j i = MixedTenMass.weighted (rows M j i) :=
  Classical.choose_spec (ten_endomorphism (entry M j i))

def matrices (M : IntertwiningMap (sourceSM p) (targetSM q)) : MatrixTenMass.Matrices p q :=
  ⟨fun j i => (rows M j i).up, fun j i => (rows M j i).quark,
    fun j i => (rows M j i).electron⟩

theorem reconstructed_map (M : IntertwiningMap (sourceSM p) (targetSM q))
    (x : MatrixTenMass.Source p) (j : Fin q) :
    M x j = ∑ i, MixedTenMass.weighted (rows M j i) (x.1 i) := by
  let P := (FiniteSpectrum.homCopies q (sourceSM p) (ten.comp hom) M) j
  have hb := bar_to_ten_zero (P.comp
    (IntertwiningMap.inr ℂ (FiniteSpectrum.copies p (ten.comp hom)) (antifundamental.comp hom)))
  have hz : P (0,x.2) = 0 := DFunLike.congr_fun hb x.2
  have hd : x = (∑ i, (copySlot p (ten.comp hom) i (x.1 i),0)) + (0,x.2) := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_sum, add_zero]
      change x.1 = ∑ i, Pi.single i (x.1 i)
      rw [Finset.univ_sum_single]
    · simp [Prod.snd_sum]
  change P x = _
  conv_lhs => rw [hd, map_add, map_sum, hz, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  exact DFunLike.congr_fun (rows_spec M j i) (x.1 i)

theorem massMap_eq (M : IntertwiningMap (MatrixTenMass.sourceRho chi psi p)
    (MatrixTenMass.targetRho chi q)) :
    MatrixTenMass.massMap chi psi (matrices (restrictMassMap chi psi M)) = M := by
  apply DFunLike.ext
  intro x
  funext j
  have he := reconstructed_map (restrictMassMap chi psi M) x j
  change (∑ i, MixedTenMass.weighted (MatrixTenMass.row (matrices (restrictMassMap chi psi M)) j i)
    (x.1 i)) = M x j
  change (∑ i, MixedTenMass.weighted (MatrixTenMass.row (matrices (restrictMassMap chi psi M)) j i)
    (x.1 i)) = (restrictMassMap chi psi M) x j
  rw [he]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1

theorem matrix_normal_form
    (B : InvariantWeylMass.SymmetricMass (MatrixTenMass.fieldsRho chi psi p q)) :
    ∃ A : MatrixTenMass.Matrices p q, B.form = (MatrixTenMass.mass chi psi A).form := by
  let M := crossMap (MatrixTenMass.sourceRho chi psi p) (MatrixTenMass.targetRho chi q) B
  refine ⟨matrices (restrictMassMap chi psi M), ?_⟩
  rw [normal_form chi psi p q B]
  change (InvariantWeylMass.ofDirac M).form =
    (InvariantWeylMass.ofDirac (MatrixTenMass.massMap chi psi (matrices (restrictMassMap chi psi M)))).form
  rw [massMap_eq]


local instance (A : MatrixTenMass.Matrices p q) (K : MatrixTenMass.Kernels A) :
    AddCommGroup (MatrixTenMass.QuarkSpace A K) := inferInstance
local instance (A : MatrixTenMass.Matrices p q) (K : MatrixTenMass.Kernels A) :
    AddCommGroup (MatrixTenMass.UpSpace A K) := inferInstance
local instance (A : MatrixTenMass.Matrices p q) (K : MatrixTenMass.Kernels A) :
    AddCommGroup (MatrixTenMass.ElectronSpace A K) := inferInstance

theorem arbitrary_mass_light_exterior
    (B : InvariantWeylMass.SymmetricMass (MatrixTenMass.fieldsRho chi psi p q))
    (h : q < p) :
    ∃ A : MatrixTenMass.Matrices p q,
      B.form = (MatrixTenMass.mass chi psi A).form ∧
      (∀ x : MatrixTenMass.QuarkSpace A (MatrixTenMass.kernels A h), x.val ∈ B.radical.toSubmodule) ∧
      (∀ x : MatrixTenMass.UpSpace A (MatrixTenMass.kernels A h), x.val ∈ B.radical.toSubmodule) ∧
      (∀ x : MatrixTenMass.ElectronSpace A (MatrixTenMass.kernels A h), x.val ∈ B.radical.toSubmodule) ∧
      PhysicalQqueEndpoint.HasExterior
        (MatrixTenMass.quarkRho chi A (MatrixTenMass.kernels A h))
        (MatrixTenMass.upLeftRho chi A (MatrixTenMass.kernels A h)).dual
        (MatrixTenMass.electronLeftRho chi A (MatrixTenMass.kernels A h)).dual := by
  obtain ⟨A,he⟩ := matrix_normal_form chi psi B
  obtain ⟨hq,hu,hl,hf⟩ := MatrixTenMass.rectangular_light_exterior chi psi A h
  have hm (x : MatrixTenMass.Fields p q) :
      x ∈ B.radical.toSubmodule ↔ x ∈ (MatrixTenMass.mass chi psi A).radical.toSubmodule := by
    rw [InvariantWeylMass.SymmetricMass.mem_radical,
      InvariantWeylMass.SymmetricMass.mem_radical, he]
  exact ⟨A,he,fun x => (hm x.val).mpr (hq x),
    fun x => (hm x.val).mpr (hu x), fun x => (hm x.val).mpr (hl x),hf⟩

end
end GUT.SU5.InvariantMassNormalForm
