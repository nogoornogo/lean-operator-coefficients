import GUT.SU6.Adapters.StandardScalarBlock
import Math.RepresentationTheory.Constructions.ScalarEigencharacter
import Physics.StandardModel.Operators.BaryonOne.Qque.NeutralQqueExterior
import Math.RepresentationTheory.Decomposition.RepresentationConjugation

open Physics

/-! Fixed-placement scalar/block residual actions, allowing projective
pointwise factors. No homomorphic SU(6) lift is supplied. -/
namespace GUT.ScalarBlockQque
set_option autoImplicit false
noncomputable section
open Math StandardSMUVFields StandardSMExterior StandardSMGaugeTensor
open SMEpsilonTensor
open scoped TensorProduct

variable (H : Type*) [CommGroup H]

/-- Hermitian direct-sum form on the three analytic summands. -/
def uvInner (x y : UV) : ℂ :=
  inner ℂ x.1.1 y.1.1 + inner ℂ x.1.2 y.1.2 + inner ℂ x.2 y.2

/-- Named evaluation of the existing exact benchmark mass. -/
def benchmarkForm (x y : UV) : ℂ := (StandardSMUVMass.mass Unit).form x y

structure Input where
  finite : Finite H
  physical : Representation ℂ H UV
  unitary : ∀ h x y, uvInner (physical h x) (physical h y) = uvInner x y
  lift : H → ActualRestriction.SU6
  a : H → Circle
  b : H → Circle
  d : H → Circle
  c : H → Circle
  w : H → Circle
  t : H → Circle
  diagonal : ∀ h, (lift h : Matrix (Fin 6) (Fin 6) ℂ) =
    Matrix.diagonal (StandardScalarBlock.coords (c h) (w h) (t h))
  physical_eq : ∀ h x, physical h x = uvRho (lift h)
    (((a h : ℂ) • x.1.1, (b h : ℂ) • x.1.2), (d h : ℂ) • x.2)
  mass_invariant : ∀ h x y, benchmarkForm (physical h x) (physical h y) = benchmarkForm x y

variable {H} (S : Input H)

theorem scalar_commutes (a b d : ℂ) (g : ActualRestriction.SU6) (x : UV) :
    uvRho g ((a • x.1.1, b • x.1.2), d • x.2) =
      ((a • (uvRho g x).1.1, b • (uvRho g x).1.2), d • (uvRho g x).2) := by
  exact Prod.ext (Prod.ext
    ((ConcreteSU6Representations.exteriorTwo.rho g).map_smul a x.1.1)
    ((ConcreteSU6Representations.antifundamental.rho g).map_smul b x.1.2))
    ((ConcreteSU6Representations.antifundamental.rho g).map_smul d x.2)

/-- Covariance uses a pointwise inner lift, without imposing its group law. -/
theorem pointwise_covariance (h : H) (g : ActualRestriction.SU6) (x : UV) :
    S.physical h (uvRho g x) =
      uvRho (S.lift h * g * (S.lift h)⁻¹) (S.physical h x) := by
  rw [S.physical_eq, S.physical_eq, ← scalar_commutes]
  have he (y : UV) :
      uvRho (S.lift h * g * (S.lift h)⁻¹) (uvRho (S.lift h) y) =
        uvRho (S.lift h) (uvRho g y) := by
    rw [← Module.End.mul_apply, ← uvRho.map_mul]
    have hg : (S.lift h * g * (S.lift h)⁻¹) * S.lift h = S.lift h * g := by group
    rw [hg, uvRho.map_mul, Module.End.mul_apply]
  exact (he _).symm

theorem diagonal_commutes (h : H) (v : Fin 6 → ℂ) :
    (S.lift h : Matrix (Fin 6) (Fin 6) ℂ) * Matrix.diagonal v =
      Matrix.diagonal v * (S.lift h : Matrix (Fin 6) (Fin 6) ℂ) := by
  rw [S.diagonal]
  simp [Matrix.diagonal_mul_diagonal, mul_comm]

/-- Neutral external action fixes every diagonal adjoint matrix. -/
theorem diagonal_fixed (h : H) (v : Fin 6 → ℂ) :
    ((S.lift h : Matrix (Fin 6) (Fin 6) ℂ) * Matrix.diagonal v) *
      (((S.lift h)⁻¹ : ActualRestriction.SU6) : Matrix (Fin 6) (Fin 6) ℂ) = Matrix.diagonal v := by
  rw [diagonal_commutes S h v, Matrix.mul_assoc, ← Submonoid.coe_mul]
  simp

theorem radical_stable (h : H) {x : UV}
    (hx : x ∈ (StandardSMUVMass.mass Unit).radical.toSubmodule) :
    S.physical h x ∈ (StandardSMUVMass.mass Unit).radical.toSubmodule := by
  rw [InvariantWeylMass.SymmetricMass.mem_radical] at hx ⊢
  intro y
  have hy : S.physical h (S.physical h⁻¹ y) = y := by simp
  rw [← hy]
  exact (S.mass_invariant h x (S.physical h⁻¹ y)).trans (hx _)

/-- The benchmark SM action on the selected fifteen is the actual UV restriction. -/
theorem on_fifteen_gauge (g : GaugeGroup) (x : Blocks) :
    uvRho (StandardSMGroup.hom g) (StandardScalarBlock.embedding x) =
      StandardScalarBlock.embedding (blocksRho g x) := by
  have he (y : Blocks) : StandardSMExterior.analyticEquiv.toLinearEquiv
      (ConcreteSU6Representations.exteriorTwo.rho (StandardSMGroup.hom g)
        (StandardSMExterior.analyticEquiv.toLinearEquiv.symm y)) = blocksRho g y := by
    have hi := Representation.IntertwiningMap.isIntertwining _ _
      StandardSMExterior.analyticEquiv.toIntertwiningMap g
      (StandardSMExterior.analyticEquiv.toLinearEquiv.symm y)
    exact hi.trans (congrArg (blocksRho g)
      (StandardSMExterior.analyticEquiv.toLinearEquiv.apply_symm_apply y))
  have ha := FirstSummandEmbedding.action
    StandardSMExterior.analyticEquiv.toLinearEquiv
    (ConcreteSU6Representations.exteriorTwo.rho (StandardSMGroup.hom g))
    (ConcreteSU6Representations.antifundamental.rho (StandardSMGroup.hom g))
    (ConcreteSU6Representations.antifundamental.rho (StandardSMGroup.hom g))
    (blocksRho g) he x
  exact ha

theorem on_fifteen (h : H) (x : Blocks) :
    S.physical h (StandardScalarBlock.embedding x) =
      StandardScalarBlock.embedding ((S.a h : ℂ) •
        StandardScalarBlock.blocks (S.c h) (S.w h) (S.t h) x) := by
  rw [S.physical_eq]
  apply FirstSummandEmbedding.scaled_action
    StandardSMExterior.analyticEquiv.toLinearEquiv
    (ConcreteSU6Representations.exteriorTwo.rho (S.lift h))
    (ConcreteSU6Representations.antifundamental.rho (S.lift h))
    (ConcreteSU6Representations.antifundamental.rho (S.lift h))
    (StandardScalarBlock.blocksLinear (S.c h) (S.w h) (S.t h))
  intro y
  have he := StandardScalarBlock.analytic_action (S.lift h)
    (S.c h) (S.w h) (S.t h) (S.diagonal h)
    (StandardSMExterior.analyticEquiv.toLinearEquiv.symm y)
  exact he.trans (congrArg (StandardScalarBlock.blocks (S.c h) (S.w h) (S.t h))
    (StandardSMExterior.analyticEquiv.toLinearEquiv.apply_symm_apply y))

def quarkVector (x : Quark) : UV := StandardScalarBlock.embedding (0, (x, 0))
def upVector (x : Module.Dual ℂ Color) : UV := StandardScalarBlock.embedding (x, 0)
def electronVector (x : Module.Dual ℂ ℂ) : UV :=
  StandardScalarBlock.embedding (0, (0, (x, 0)))

theorem quark_mem_radical (x : Quark) :
    quarkVector x ∈ (StandardSMUVMass.mass Unit).radical.toSubmodule :=
  StandardScalarBlock.embedding_mem_radical _ rfl rfl

theorem up_mem_radical (x : Module.Dual ℂ Color) :
    upVector x ∈ (StandardSMUVMass.mass Unit).radical.toSubmodule :=
  StandardScalarBlock.embedding_mem_radical _ rfl rfl

theorem electron_mem_radical (x : Module.Dual ℂ ℂ) :
    electronVector x ∈ (StandardSMUVMass.mass Unit).radical.toSubmodule :=
  StandardScalarBlock.embedding_mem_radical _ rfl rfl

theorem quark_action (h : H) (x : Quark) :
    S.physical h (quarkVector x) =
      ((S.a h * S.c h * S.w h : Circle) : ℂ) • quarkVector x := by
  simp only [quarkVector]
  rw [(on_fifteen S), ← StandardScalarBlock.embedding_smul]
  apply congrArg StandardScalarBlock.embedding
  simp [StandardScalarBlock.blocks, smul_smul, mul_assoc]

theorem up_action (h : H) (x : Module.Dual ℂ Color) :
    S.physical h (upVector x) =
      ((S.a h * S.c h * S.c h : Circle) : ℂ) • upVector x := by
  simp only [upVector]
  rw [(on_fifteen S), ← StandardScalarBlock.embedding_smul]
  apply congrArg StandardScalarBlock.embedding
  simp [StandardScalarBlock.blocks, smul_smul, mul_assoc]

theorem electron_action (h : H) (x : Module.Dual ℂ ℂ) :
    S.physical h (electronVector x) =
      ((S.a h * S.w h * S.w h : Circle) : ℂ) • electronVector x := by
  simp only [electronVector]
  rw [(on_fifteen S), ← StandardScalarBlock.embedding_smul]
  apply congrArg StandardScalarBlock.embedding
  simp [StandardScalarBlock.blocks, smul_smul, mul_assoc]

def quarkLinear : Quark →ₗ[ℂ] UV where
  toFun := quarkVector
  map_add' x y := by
    simpa [quarkVector] using StandardScalarBlock.embedding_add (0, (x, 0)) (0, (y, 0))
  map_smul' r x := by
    simpa [quarkVector] using StandardScalarBlock.embedding_smul r (0, (x, 0))

def upLinear : Module.Dual ℂ Color →ₗ[ℂ] UV where
  toFun := upVector
  map_add' x y := by
    simpa [upVector] using StandardScalarBlock.embedding_add (x, 0) (y, 0)
  map_smul' r x := by
    simpa [upVector] using StandardScalarBlock.embedding_smul r (x, 0)

def electronLinear : Module.Dual ℂ ℂ →ₗ[ℂ] UV where
  toFun := electronVector
  map_add' x y := by
    simpa [electronVector] using StandardScalarBlock.embedding_add (0, (0, (x, 0))) (0, (0, (y, 0)))
  map_smul' r x := by
    simpa [electronVector] using StandardScalarBlock.embedding_smul r (0, (0, (x, 0)))

theorem quark_gauge_action (g : GaugeGroup) (x : Quark) :
    uvRho (StandardSMGroup.hom g) (quarkLinear x) = quarkLinear (quark g x) := by
  have hb : blocksRho g (0, (x, 0)) = (0, (quark g x, 0)) := by simp [blocksRho]
  exact (on_fifteen_gauge g (0, (x, 0))).trans (congrArg StandardScalarBlock.embedding hb)

theorem up_gauge_action (g : GaugeGroup) (x : Module.Dual ℂ Color) :
    uvRho (StandardSMGroup.hom g) (upLinear x) = upLinear (upRight.dual g x) := by
  have hb : blocksRho g (x, 0) = (upRight.dual g x, 0) := by simp [blocksRho]
  exact (on_fifteen_gauge g (x, 0)).trans (congrArg StandardScalarBlock.embedding hb)

theorem electron_gauge_action (g : GaugeGroup) (x : Module.Dual ℂ ℂ) :
    uvRho (StandardSMGroup.hom g) (electronLinear x) =
      electronLinear (electronRight.dual g x) := by
  have hb : blocksRho g (0, (0, (x, 0))) = (0, (0, (electronRight.dual g x, 0))) := by
    simp [blocksRho]
  exact (on_fifteen_gauge g (0, (0, (x, 0)))).trans (congrArg StandardScalarBlock.embedding hb)

theorem quark_injective : Function.Injective quarkLinear := by
  intro x y h
  exact congrArg (fun z : Blocks => z.2.1) (StandardScalarBlock.embedding_injective h)

theorem up_injective : Function.Injective upLinear := by
  intro x y h
  exact congrArg (fun z : Blocks => z.1) (StandardScalarBlock.embedding_injective h)

theorem electron_injective : Function.Injective electronLinear := by
  intro x y h
  exact congrArg (fun z : Blocks => z.2.2.1) (StandardScalarBlock.embedding_injective h)

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

theorem exists_standard_exterior :
    ∃ f : QqueSpinorExterior.ExteriorCoefficient
      (NeutralQqueExterior.q (charges S)) (NeutralQqueExterior.u (charges S))
      (NeutralQqueExterior.e (charges S)), f ≠ 0 :=
  ⟨NeutralQqueExterior.coefficient (charges S) (neutral S),
    NeutralQqueExterior.coefficient_nonzero (charges S) (neutral S)⟩

abbrev QuarkSpace := LinearMap.range quarkLinear
abbrev UpSpace := LinearMap.range upLinear
abbrev ElectronSpace := LinearMap.range electronLinear

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

theorem quarkSpace_light (x : QuarkSpace) :
    x.val ∈ (StandardSMUVMass.mass Unit).radical.toSubmodule := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact quark_mem_radical y
theorem upSpace_light (x : UpSpace) :
    x.val ∈ (StandardSMUVMass.mass Unit).radical.toSubmodule := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact up_mem_radical y
theorem electronSpace_light (x : ElectronSpace) :
    x.val ∈ (StandardSMUVMass.mass Unit).radical.toSubmodule := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact electron_mem_radical y

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
    (quarkRho S (g, 1) x).val = uvRho (StandardSMGroup.hom g) x.val := by
  rw [quarkRho, RepresentationConjugation.pullback_apply,
    NeutralQqueExterior.charged_apply]
  simp only [map_one, Circle.coe_one, one_smul]
  change quarkLinear (quark g (quarkCoords x)) = _
  exact (quark_gauge_action g (quarkCoords x)).symm.trans
    (congrArg (uvRho (StandardSMGroup.hom g)) (quark_coords x))

theorem up_gauge_restriction (g : GaugeGroup) (x : UpSpace) :
    (upLeftRho S (g, 1) x).val = uvRho (StandardSMGroup.hom g) x.val := by
  rw [upLeftRho, RepresentationConjugation.pullback_apply,
    NeutralQqueExterior.charged_apply]
  simp only [map_one, Circle.coe_one, one_smul]
  change upLinear (upRight.dual g (upCoords x)) = _
  exact (up_gauge_action g (upCoords x)).symm.trans
    (congrArg (uvRho (StandardSMGroup.hom g)) (up_coords x))

theorem electron_gauge_restriction (g : GaugeGroup) (x : ElectronSpace) :
    (electronLeftRho S (g, 1) x).val = uvRho (StandardSMGroup.hom g) x.val := by
  rw [electronLeftRho, RepresentationConjugation.pullback_apply,
    NeutralQqueExterior.charged_apply]
  simp only [map_one, Circle.coe_one, one_smul]
  change electronLinear (electronRight.dual g (electronCoords x)) = _
  exact (electron_gauge_action g (electronCoords x)).symm.trans
    (congrArg (uvRho (StandardSMGroup.hom g)) (electron_coords x))

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

end
end GUT.ScalarBlockQque
