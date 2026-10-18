import Math.RepresentationTheory.Unitary.CommutingUnitaryActions
import Physics.FieldTheory.Mass.InvariantWeylMass
import GUT.SU5.Branching.ExteriorSquare
import GUT.SU5.Representations.UnitaryMatter
import Math.RepresentationTheory.ScalarEigencharacter
import Physics.StandardModel.Operators.NeutralQqueExterior
import Math.RepresentationTheory.Decomposition.RepresentationConjugation

/-! Actual SU(5) scalar/block branching and physical qque on the ranges
of the participating field embeddings. Auxiliary factors are pointwise. -/
namespace GUT.SU5.ScalarBlockQque
set_option autoImplicit false
noncomputable section
open Math StandardModelEmbedding Matter StandardSMGaugeTensor SMEpsilonTensor
open ExteriorSquareBranching
open scoped TensorProduct
local instance : AddCommGroup Quark := inferInstance

def coords (c w : ℂ) : Fin 5 → ℂ := ![c,c,c,w,w]
def fiveBlocks (c w : ℂ) (x : FundamentalBranching.Blocks) := (c • x.1, w • x.2)
def blocks (c w : ℂ) (x : Blocks) :=
  ((c*c) • x.1, ((c*w) • x.2.1, (w*w) • x.2.2))

theorem fundamental_action (s : TargetGroup) (c w : ℂ)
    (hs : (s : Matrix (Fin 5) (Fin 5) ℂ) = Matrix.diagonal (coords c w)) (v : Five) :
    FundamentalBranching.splitEquiv (fundamental s v) =
      fiveBlocks c w (FundamentalBranching.splitEquiv v) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [FundamentalBranching.splitEquiv, fundamental, Matrix.toLin'_apply,
      hs, fiveBlocks, coords, Matrix.mulVec_diagonal]

theorem pair_action (c w : ℂ) (x y : FundamentalBranching.Blocks) :
    pair (fiveBlocks c w x) (fiveBlocks c w y) = blocks c w (pair x y) := by
  simp [pair, fiveBlocks, blocks, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_sub, smul_smul, mul_comm, mul_left_comm, mul_assoc, eps2, mul_sub]

def blocksLinear (c w : ℂ) : Blocks →ₗ[ℂ] Blocks where
  toFun := blocks c w
  map_add' x y := by simp [blocks, smul_add]
  map_smul' z x := by simp [blocks, smul_smul, mul_comm]

theorem branch_action (s : TargetGroup) (c w : ℂ)
    (hs : (s : Matrix (Fin 5) (Fin 5) ℂ) = Matrix.diagonal (coords c w)) (v : Ten) :
    branch (ten s v) = blocks c w (branch v) := by
  have he : branch.comp (ten s) = (blocksLinear c w).comp branch := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    change branch (exteriorPower.map 2 (fundamental s) (exteriorPower.ιMulti ℂ 2 f)) =
      blocks c w (branch (exteriorPower.ιMulti ℂ 2 f))
    rw [exteriorPower.map_apply_ιMulti, branch_wedge, branch_wedge]
    change pair (FundamentalBranching.splitEquiv (fundamental s (f 0)))
      (FundamentalBranching.splitEquiv (fundamental s (f 1))) = _
    rw [fundamental_action s c w hs, fundamental_action s c w hs]
    exact pair_action c w _ _
  exact LinearMap.congr_fun he v

local instance : AddCommGroup Ten := inferInstance
private theorem index_symm (i : Fin 5) : blockIndexEquiv.symm i =
    ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1] i := by
  fin_cases i <;> rfl

theorem diagonal_commutes (s : TargetGroup) (c w : ℂ)
    (hs : (s : Matrix (Fin 5) (Fin 5) ℂ) = Matrix.diagonal (coords c w))
    (g : GaugeGroup) : Commute s (hom g) := by
  apply Subtype.ext
  change (s : Matrix (Fin 5) (Fin 5) ℂ) * matrixHom g =
    matrixHom g * (s : Matrix (Fin 5) (Fin 5) ℂ)
  rw [hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, coords, matrixHom, rawHom,
      rawMatrix, index_symm, mul_comm]

abbrev UV := Ten × BarFive
local instance : AddCommGroup UV := inferInstance
def uvRho := ten.prod antifundamental

def uvInner (x y : UV) : ℂ :=
  inner ℂ (UnitaryMatter.tenEquiv x.1) (UnitaryMatter.tenEquiv y.1) +
    inner ℂ (UnitaryMatter.antifundamentalEquiv x.2) (UnitaryMatter.antifundamentalEquiv y.2)

variable (H : Type*) [CommGroup H]
structure Input where
  finite : Finite H
  physical : Representation ℂ H UV
  unitary : ∀ h x y, uvInner (physical h x) (physical h y) = uvInner x y
  lift : H → TargetGroup
  a : H → Circle
  b : H → Circle
  c : H → Circle
  w : H → Circle
  diagonal : ∀ h, (lift h : Matrix (Fin 5) (Fin 5) ℂ) =
    Matrix.diagonal (coords (c h) (w h))
  physical_eq : ∀ h x, physical h x = uvRho (lift h) ((a h : ℂ) • x.1, (b h : ℂ) • x.2)

local instance : Nontrivial Quark := by
  apply Module.nontrivial_of_finrank_pos (R := ℂ)
  simp [Quark, Color, Weak, Module.finrank_tensorProduct]

variable {H} (S : Input H)

def externalLinear (a b : ℂ) : UV →ₗ[ℂ] UV :=
  (a • (LinearMap.id : Ten →ₗ[ℂ] Ten)).prodMap
    (b • (LinearMap.id : BarFive →ₗ[ℂ] BarFive))

theorem physical_commutes_sm (h : H) (g : GaugeGroup) :
    Commute (S.physical h) (uvRho (hom g)) := by
  have hg := (diagonal_commutes (S.lift h) (S.c h) (S.w h) (S.diagonal h) g).map uvRho
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hg.eq
    ((S.a h : ℂ) • x.1, (S.b h : ℂ) • x.2)
  change uvRho (S.lift h) (uvRho (hom g) _) = uvRho (hom g) (uvRho (S.lift h) _) at hx
  simpa [S.physical_eq, uvRho, map_smul] using hx

def joint : Representation ℂ (GaugeGroup × H) UV :=
  (uvRho.comp hom).noncommCoprod S.physical
    (fun g h => (physical_commutes_sm S h g).symm)

def embedding : Blocks →ₗ[ℂ] UV :=
  (LinearMap.inl ℂ Ten BarFive).comp tenEquiv.toLinearEquiv.symm.toLinearMap

theorem embedding_injective : Function.Injective embedding := by
  intro x y h
  exact tenEquiv.toLinearEquiv.symm.injective (congrArg Prod.fst h)

theorem embedding_action (h : H) (x : Blocks) :
    S.physical h (embedding x) = embedding ((S.a h : ℂ) • blocks (S.c h) (S.w h) x) := by
  rw [S.physical_eq]
  apply Prod.ext
  · change ten (S.lift h) ((S.a h : ℂ) • tenEquiv.toLinearEquiv.symm x) =
      tenEquiv.toLinearEquiv.symm ((S.a h : ℂ) • blocks (S.c h) (S.w h) x)
    apply tenEquiv.toLinearEquiv.injective
    rw [map_smul, map_smul, LinearEquiv.apply_symm_apply]
    change (S.a h : ℂ) • branch (ten (S.lift h) (tenEquiv.toLinearEquiv.symm x)) = _
    rw [branch_action _ _ _ (S.diagonal h)]
    exact congrArg (fun z => (S.a h : ℂ) • blocks (S.c h) (S.w h) z)
      (tenEquiv.toLinearEquiv.apply_symm_apply x)
  · simp [embedding, uvRho]

def quarkLinear : Quark →ₗ[ℂ] UV :=
  embedding.comp ((LinearMap.inr ℂ (Module.Dual ℂ Color)
    (Quark × Module.Dual ℂ ℂ)).comp (LinearMap.inl ℂ Quark (Module.Dual ℂ ℂ)))
def upLinear : Module.Dual ℂ Color →ₗ[ℂ] UV :=
  embedding.comp (LinearMap.inl ℂ (Module.Dual ℂ Color) (Quark × Module.Dual ℂ ℂ))
def electronLinear : Module.Dual ℂ ℂ →ₗ[ℂ] UV :=
  embedding.comp ((LinearMap.inr ℂ (Module.Dual ℂ Color)
    (Quark × Module.Dual ℂ ℂ)).comp (LinearMap.inr ℂ Quark (Module.Dual ℂ ℂ)))

theorem quark_injective : Function.Injective quarkLinear := by
  intro x y h
  exact congrArg (fun z : Blocks => z.2.1) (embedding_injective h)

theorem quark_action (h : H) (x : Quark) :
    S.physical h (quarkLinear x) = (S.a h * S.c h * S.w h : ℂ) • quarkLinear x := by
  have he := embedding_action S h (0, (x, 0))
  change S.physical h (quarkLinear x) = embedding ((S.a h : ℂ) • blocks (S.c h) (S.w h) (0, (x, 0))) at he
  rw [he]
  simp [quarkLinear, blocks, ← map_smul, smul_smul, mul_assoc]

theorem quark_gauge_action (g : GaugeGroup) (x : Quark) :
    uvRho (hom g) (quarkLinear x) = quarkLinear (quark g x) := by
  apply Prod.ext
  · change ten (hom g) (tenEquiv.toLinearEquiv.symm (0, (x, 0))) =
      tenEquiv.toLinearEquiv.symm _
    apply tenEquiv.toLinearEquiv.injective
    have he := tenEquiv.toIntertwiningMap.isIntertwining _ _ g (tenEquiv.toLinearEquiv.symm (0, (x, 0)))
    change tenEquiv.toLinearEquiv (ten (hom g) (tenEquiv.toLinearEquiv.symm (0, (x, 0)))) =
      blocksRho g (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (0, (x, 0)))) at he
    rw [LinearEquiv.apply_symm_apply] at he
    change tenEquiv.toLinearEquiv _ = tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm _)
    rw [LinearEquiv.apply_symm_apply]
    simpa [blocksRho, Prod.zero_eq_mk] using he
  · simp [uvRho, quarkLinear, embedding]

theorem up_injective : Function.Injective upLinear := by
  intro x y h
  exact congrArg (fun z : Blocks => z.1) (embedding_injective h)

theorem up_action (h : H) (x : Module.Dual ℂ Color) :
    S.physical h (upLinear x) = (S.a h * S.c h * S.c h : ℂ) • upLinear x := by
  have he := embedding_action S h (x, 0)
  change S.physical h (upLinear x) = embedding ((S.a h : ℂ) • blocks (S.c h) (S.w h) (x, 0)) at he
  rw [he]
  simp [upLinear, blocks, ← map_smul, smul_smul, mul_assoc, Prod.zero_eq_mk]

theorem up_gauge_action (g : GaugeGroup) (x : Module.Dual ℂ Color) :
    uvRho (hom g) (upLinear x) = upLinear (upRight.dual g x) := by
  apply Prod.ext
  · change ten (hom g) (tenEquiv.toLinearEquiv.symm (x, 0)) =
      tenEquiv.toLinearEquiv.symm _
    apply tenEquiv.toLinearEquiv.injective
    have he := tenEquiv.toIntertwiningMap.isIntertwining _ _ g (tenEquiv.toLinearEquiv.symm (x, 0))
    change tenEquiv.toLinearEquiv (ten (hom g) (tenEquiv.toLinearEquiv.symm (x, 0))) =
      blocksRho g (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (x, 0))) at he
    rw [LinearEquiv.apply_symm_apply] at he
    change tenEquiv.toLinearEquiv _ = tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm _)
    rw [LinearEquiv.apply_symm_apply]
    simpa [blocksRho, Prod.zero_eq_mk] using he
  · simp [uvRho, upLinear, embedding]

theorem electron_injective : Function.Injective electronLinear := by
  intro x y h
  exact congrArg (fun z : Blocks => z.2.2) (embedding_injective h)

theorem electron_action (h : H) (x : Module.Dual ℂ ℂ) :
    S.physical h (electronLinear x) = (S.a h * S.w h * S.w h : ℂ) • electronLinear x := by
  have he := embedding_action S h (0, (0, x))
  change S.physical h (electronLinear x) = embedding ((S.a h : ℂ) • blocks (S.c h) (S.w h) (0, (0, x))) at he
  rw [he]
  simp [electronLinear, blocks, ← map_smul, smul_smul, mul_assoc]

theorem electron_gauge_action (g : GaugeGroup) (x : Module.Dual ℂ ℂ) :
    uvRho (hom g) (electronLinear x) = electronLinear (electronRight.dual g x) := by
  apply Prod.ext
  · change ten (hom g) (tenEquiv.toLinearEquiv.symm (0, (0, x))) =
      tenEquiv.toLinearEquiv.symm _
    apply tenEquiv.toLinearEquiv.injective
    have he := tenEquiv.toIntertwiningMap.isIntertwining _ _ g (tenEquiv.toLinearEquiv.symm (0, (0, x)))
    change tenEquiv.toLinearEquiv (ten (hom g) (tenEquiv.toLinearEquiv.symm (0, (0, x)))) =
      blocksRho g (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (0, (0, x)))) at he
    rw [LinearEquiv.apply_symm_apply] at he
    change tenEquiv.toLinearEquiv _ = tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm _)
    rw [LinearEquiv.apply_symm_apply]
    simpa [blocksRho, Prod.zero_eq_mk] using he
  · simp [uvRho, electronLinear, embedding]

def quarkCharacter : H →* Circle :=
  ScalarEigencharacter.onEmbedding S.physical (fun h => S.a h * S.c h * S.w h)
    quarkLinear quark_injective (quark_action S)

def upCharacter : H →* Circle :=
  ScalarEigencharacter.onEmbedding S.physical (fun h => S.a h * S.c h * S.c h)
    upLinear up_injective (up_action S)

def electronCharacter : H →* Circle :=
  ScalarEigencharacter.onEmbedding S.physical (fun h => S.a h * S.w h * S.w h)
    electronLinear electron_injective (electron_action S)

/-- The d/L entries are unused placeholders, not their physical charges. -/
def charges : StandardBranchProtonObstruction.Charges
    (Math.FiniteAbelianChargeSectors.ChargeLabel H) where
  quark := Additive.ofMul (quarkCharacter S)
  up := Additive.ofMul (upCharacter S)
  electron := Additive.ofMul (electronCharacter S)
  down := 0
  lepton := 0

theorem neutral : FiniteAbelianChargeSectors.protonFirstCharacter (charges S) = 1 :=
  NeutralQqueExterior.neutral_of_pointwise_block (charges S) S.a S.c S.w
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

abbrev QuarkSpace := LinearMap.range quarkLinear
abbrev UpSpace := LinearMap.range upLinear
abbrev ElectronSpace := LinearMap.range electronLinear
local instance : AddCommGroup QuarkSpace := inferInstance
local instance : AddCommGroup UpSpace := inferInstance
local instance : AddCommGroup ElectronSpace := inferInstance

def quarkCoords : QuarkSpace ≃ₗ[ℂ] Quark :=
  (LinearEquiv.ofInjective quarkLinear quark_injective).symm
def upCoords : UpSpace ≃ₗ[ℂ] Module.Dual ℂ Color :=
  (LinearEquiv.ofInjective upLinear up_injective).symm
def electronCoords : ElectronSpace ≃ₗ[ℂ] Module.Dual ℂ ℂ :=
  (LinearEquiv.ofInjective electronLinear electron_injective).symm

theorem quark_coords (x : QuarkSpace) : quarkLinear (quarkCoords x) = x.val :=
  congrArg Subtype.val (quarkCoords.symm_apply_apply x)
theorem up_coords (x : UpSpace) : upLinear (upCoords x) = x.val :=
  congrArg Subtype.val (upCoords.symm_apply_apply x)
theorem electron_coords (x : ElectronSpace) : electronLinear (electronCoords x) = x.val :=
  congrArg Subtype.val (electronCoords.symm_apply_apply x)

def quarkRho := RepresentationConjugation.pullback quarkCoords
  (NeutralQqueExterior.q (charges S))
def upLeftRho := RepresentationConjugation.pullback upCoords
  (StandardSMResidualTensor.charged upRight.dual (upCharacter S))
def electronLeftRho := RepresentationConjugation.pullback electronCoords
  (StandardSMResidualTensor.charged electronRight.dual (electronCharacter S))

theorem quark_residual_action (h : H) (x : QuarkSpace) :
    ((quarkRho S) (1,h) x).val = S.physical h x.val := by
  rw [quarkRho, RepresentationConjugation.pullback_apply]
  rw [NeutralQqueExterior.charged_apply]
  simp only [map_one, Module.End.one_apply]
  rw [map_smul]
  rw [quarkCoords.symm_apply_apply]
  simp only [Submodule.coe_smul]
  change ((quarkCharacter S h : ℂ) • x.val) = S.physical h x.val
  have he := quark_action S h (quarkCoords x)
  change S.physical h (quarkLinear (quarkCoords x)) =
    (quarkCharacter S h : ℂ) • quarkLinear (quarkCoords x) at he
  rw [quark_coords] at he
  exact he.symm

theorem up_residual_action (h : H) (x : UpSpace) :
    ((upLeftRho S) (1,h) x).val = S.physical h x.val := by
  rw [upLeftRho, RepresentationConjugation.pullback_apply]
  rw [NeutralQqueExterior.charged_apply]
  simp only [map_one, Module.End.one_apply]
  rw [map_smul]
  rw [upCoords.symm_apply_apply]
  simp only [Submodule.coe_smul]
  change ((upCharacter S h : ℂ) • x.val) = S.physical h x.val
  have he := up_action S h (upCoords x)
  change S.physical h (upLinear (upCoords x)) =
    (upCharacter S h : ℂ) • upLinear (upCoords x) at he
  rw [up_coords] at he
  exact he.symm

theorem electron_residual_action (h : H) (x : ElectronSpace) :
    ((electronLeftRho S) (1,h) x).val = S.physical h x.val := by
  rw [electronLeftRho, RepresentationConjugation.pullback_apply]
  rw [NeutralQqueExterior.charged_apply]
  simp only [map_one, Module.End.one_apply]
  rw [map_smul]
  rw [electronCoords.symm_apply_apply]
  simp only [Submodule.coe_smul]
  change ((electronCharacter S h : ℂ) • x.val) = S.physical h x.val
  have he := electron_action S h (electronCoords x)
  change S.physical h (electronLinear (electronCoords x)) =
    (electronCharacter S h : ℂ) • electronLinear (electronCoords x) at he
  rw [electron_coords] at he
  exact he.symm

theorem quark_gauge_restriction (g : GaugeGroup) (x : QuarkSpace) :
    (quarkRho S (g, 1) x).val = uvRho (hom g) x.val := by
  rw [quarkRho, RepresentationConjugation.pullback_apply,
    NeutralQqueExterior.charged_apply]
  simp only [map_one, Circle.coe_one, one_smul]
  change quarkLinear (quark g (quarkCoords x)) = _
  exact (quark_gauge_action g (quarkCoords x)).symm.trans
    (congrArg (uvRho (hom g)) (quark_coords x))

theorem up_gauge_restriction (g : GaugeGroup) (x : UpSpace) :
    (upLeftRho S (g, 1) x).val = uvRho (hom g) x.val := by
  rw [upLeftRho, RepresentationConjugation.pullback_apply,
    NeutralQqueExterior.charged_apply]
  simp only [map_one, Circle.coe_one, one_smul]
  change upLinear (upRight.dual g (upCoords x)) = _
  exact (up_gauge_action g (upCoords x)).symm.trans
    (congrArg (uvRho (hom g)) (up_coords x))

theorem electron_gauge_restriction (g : GaugeGroup) (x : ElectronSpace) :
    (electronLeftRho S (g, 1) x).val = uvRho (hom g) x.val := by
  rw [electronLeftRho, RepresentationConjugation.pullback_apply,
    NeutralQqueExterior.charged_apply]
  simp only [map_one, Circle.coe_one, one_smul]
  change electronLinear (electronRight.dual g (electronCoords x)) = _
  exact (electron_gauge_action g (electronCoords x)).symm.trans
    (congrArg (uvRho (hom g)) (electron_coords x))

theorem quark_joint_action (g : GaugeGroup) (h : H) (x : QuarkSpace) :
    (quarkRho S (g,h) x).val = joint S (g,h) x.val := by
  have he := LinearMap.congr_fun ((quarkRho S).map_mul (g,1) (1,h)) x
  simp only [Prod.mk_mul_mk, mul_one, one_mul, Module.End.mul_apply] at he
  change quarkRho S (g,h) x = quarkRho S (g,1) (quarkRho S (1,h) x) at he
  rw [he]
  rw [quark_gauge_restriction, quark_residual_action]
  rfl

theorem up_joint_action (g : GaugeGroup) (h : H) (x : UpSpace) :
    (upLeftRho S (g,h) x).val = joint S (g,h) x.val := by
  have he := LinearMap.congr_fun ((upLeftRho S).map_mul (g,1) (1,h)) x
  simp only [Prod.mk_mul_mk, mul_one, one_mul, Module.End.mul_apply] at he
  change upLeftRho S (g,h) x = upLeftRho S (g,1) (upLeftRho S (1,h) x) at he
  rw [he]
  rw [up_gauge_restriction, up_residual_action]
  rfl

theorem electron_joint_action (g : GaugeGroup) (h : H) (x : ElectronSpace) :
    (electronLeftRho S (g,h) x).val = joint S (g,h) x.val := by
  have he := LinearMap.congr_fun ((electronLeftRho S).map_mul (g,1) (1,h)) x
  simp only [Prod.mk_mul_mk, mul_one, one_mul, Module.End.mul_apply] at he
  change electronLeftRho S (g,h) x = electronLeftRho S (g,1) (electronLeftRho S (1,h) x) at he
  rw [he]
  rw [electron_gauge_restriction, electron_residual_action]
  rfl

def quarkEq : Representation.Equiv (quarkRho S) (NeutralQqueExterior.q (charges S)) :=
  RepresentationConjugation.equiv quarkCoords _

def upEq : Representation.Equiv (upLeftRho S).dual (NeutralQqueExterior.u (charges S)) := by
  have eq := SplitRepresentationProjection.dualEquiv
    (RepresentationConjugation.equiv upCoords
      (StandardSMResidualTensor.charged upRight.dual (upCharacter S)))
  rw [NeutralQqueExterior.charged_dual] at eq
  exact eq.trans (NeutralQqueExterior.chargedEquiv
    (SplitRepresentationProjection.bidualEquiv upRight).symm (upCharacter S)⁻¹)

def electronEq : Representation.Equiv (electronLeftRho S).dual
    (NeutralQqueExterior.e (charges S)) := by
  have eq := SplitRepresentationProjection.dualEquiv
    (RepresentationConjugation.equiv electronCoords
      (StandardSMResidualTensor.charged electronRight.dual (electronCharacter S)))
  rw [NeutralQqueExterior.charged_dual] at eq
  exact eq.trans (NeutralQqueExterior.chargedEquiv
    (SplitRepresentationProjection.bidualEquiv electronRight).symm (electronCharacter S)⁻¹)

theorem exists_actual_exterior :
    ∃ f : QqueSpinorExterior.ExteriorCoefficient (quarkRho S)
      (upLeftRho S).dual (electronLeftRho S).dual, f ≠ 0 :=
  NeutralQqueExterior.exists_on_fields (charges S) (neutral S)
    (quarkRho S) (upLeftRho S).dual (electronLeftRho S).dual (quarkEq S) (upEq S) (electronEq S)

/-- Identity residual action supplies an inhabited unitary zero-mass control. -/
def trivialInput (H : Type*) [CommGroup H] [Finite H] : Input H where
  finite := inferInstance
  physical := Representation.trivial ℂ H UV
  unitary := by intros; rfl
  lift := fun _ => 1
  a := fun _ => 1
  b := fun _ => 1
  c := fun _ => 1
  w := fun _ => 1
  diagonal := by intro h; ext i j; fin_cases i <;> fin_cases j <;> simp [coords, Matrix.diagonal]
  physical_eq := by intro h x; simp [uvRho]

def zeroMass := InvariantWeylMass.SymmetricMass.zero (uvRho.comp hom)

theorem zeroMass_light (x : UV) : x ∈ zeroMass.radical.toSubmodule := by
  rw [InvariantWeylMass.SymmetricMass.mem_radical]
  intro y
  rfl

/-- No particular mass formula is required once actual participating zero
modes have been certified. Invariance under H derives radical stability. -/
structure LightMass (S : Input H) where
  mass : InvariantWeylMass.SymmetricMass S.physical
  gauge_invariant : ∀ g x y, mass.form (uvRho (hom g) x) (uvRho (hom g) y) = mass.form x y
  quark_light : ∀ x, quarkLinear x ∈ mass.radical.toSubmodule
  up_light : ∀ x, upLinear x ∈ mass.radical.toSubmodule
  electron_light : ∀ x, electronLinear x ∈ mass.radical.toSubmodule

def LightMass.jointMass (B : LightMass S) : InvariantWeylMass.SymmetricMass (joint S) where
  form := B.mass.form
  symmetric := B.mass.symmetric
  invariant := by
    intro g x y
    change B.mass.form (uvRho (hom g.1) (S.physical g.2 x))
      (uvRho (hom g.1) (S.physical g.2 y)) = _
    rw [B.gauge_invariant, B.mass.invariant]

theorem LightMass.joint_radical (B : LightMass S) :
    (B.jointMass).radical.toSubmodule = B.mass.radical.toSubmodule := by
  ext x
  rw [InvariantWeylMass.SymmetricMass.mem_radical,
    InvariantWeylMass.SymmetricMass.mem_radical]
  rfl

theorem radical_stable (B : LightMass S) (h : H) (x : UV)
    (hx : x ∈ B.mass.radical.toSubmodule) :
    S.physical h x ∈ B.mass.radical.toSubmodule :=
  B.mass.radical.apply_mem_toSubmodule h hx

theorem quarkSpace_light (B : LightMass S) (x : QuarkSpace) :
    x.val ∈ B.mass.radical.toSubmodule := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact B.quark_light y

theorem upSpace_light (B : LightMass S) (x : UpSpace) :
    x.val ∈ B.mass.radical.toSubmodule := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact B.up_light y

theorem electronSpace_light (B : LightMass S) (x : ElectronSpace) :
    x.val ∈ B.mass.radical.toSubmodule := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact B.electron_light y

def zeroLightMass : LightMass S where
  mass := InvariantWeylMass.SymmetricMass.zero S.physical
  gauge_invariant := by intros; rfl
  quark_light := by intro x; rw [InvariantWeylMass.SymmetricMass.mem_radical]; intro y; rfl
  up_light := by intro x; rw [InvariantWeylMass.SymmetricMass.mem_radical]; intro y; rfl
  electron_light := by intro x; rw [InvariantWeylMass.SymmetricMass.mem_radical]; intro y; rfl

/-- The coefficient acts on the participating ranges, all certified light;
no extension to an untyped exterior power of the all-left radical is asserted. -/
theorem exists_light_exterior (B : LightMass S) :
    (∀ x : QuarkSpace, x.val ∈ B.mass.radical.toSubmodule) ∧
    (∀ x : UpSpace, x.val ∈ B.mass.radical.toSubmodule) ∧
    (∀ x : ElectronSpace, x.val ∈ B.mass.radical.toSubmodule) ∧
    ∃ f : QqueSpinorExterior.ExteriorCoefficient (quarkRho S)
      (upLeftRho S).dual (electronLeftRho S).dual, f ≠ 0 :=
  ⟨quarkSpace_light S B, upSpace_light S B, electronSpace_light S B, exists_actual_exterior S⟩

end
end GUT.SU5.ScalarBlockQque
