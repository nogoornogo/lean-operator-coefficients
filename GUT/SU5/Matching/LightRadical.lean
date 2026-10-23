import GUT.SU5.SelectionRules.GeorgiGlashowSource
import GUT.SU5.Matching.MediatorMatching

open Physics

open Math

/-! Actual currents on the existing zero-mass radical. The same ten-space
operator acts in every generation; the bar-five component is untouched. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU5.LightRadical
noncomputable section
open MatterSource GeorgiGlashowSource HeavyCurrents
open ExteriorSquareCoordinates (infinitesimal)
open SMEpsilonTensor StandardSMGaugeTensor
open scoped TensorProduct

variable {H : Type*} [Group H] {n : ℕ} (R : OrdinaryAction H n)

abbrev Light := (GeorgiGlashowSource.mass R).radical.toSubmodule

def tenOperator (F : Matter.Ten →ₗ[ℂ] Matter.Ten) :
    UnitaryMatter.TenHilbert →ₗ[ℂ] UnitaryMatter.TenHilbert :=
  UnitaryMatter.tenEquiv.toLinearMap.comp
    (F.comp UnitaryMatter.tenEquiv.symm.toLinearMap)

def onMatter (F : Matter.Ten →ₗ[ℂ] Matter.Ten) : Space n →ₗ[ℂ] Space n where
  toFun x := WithLp.toLp 2 fun i => WithLp.toLp 2 fun a => match i with
    | .ten => tenOperator F (x .ten a)
    | .barFive => 0
  map_add' x y := by
    apply (WithLp.equiv 2 _).injective
    funext i
    apply (WithLp.equiv 2 _).injective
    funext a
    cases i
    · exact map_add (tenOperator F) _ _
    · exact (zero_add _).symm
  map_smul' z x := by
    apply (WithLp.equiv 2 _).injective
    funext i
    apply (WithLp.equiv 2 _).injective
    funext a
    cases i
    · exact map_smul (tenOperator F) _ _
    · exact (smul_zero z).symm

theorem onMatter_commutes (F : Matter.Ten →ₗ[ℂ] Matter.Ten) (h : H) (x : Space n) :
    onMatter F (residual R h x) = residual R h (onMatter F x) := by
  apply (WithLp.equiv 2 _).injective
  funext i
  apply (WithLp.equiv 2 _).injective
  funext a
  cases i with
  | ten =>
    change tenOperator F ((R h).val.val x .ten a) = (R h).val.val (onMatter F x) .ten a
    rw [action_eq_multiplicity, action_eq_multiplicity]
    change tenOperator F (∑ b, _ • x .ten b) = ∑ b, _ • tenOperator F (x .ten b)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro b _
    exact map_smul (tenOperator F) _ _
  | barFive =>
    change 0 = (R h).val.val (onMatter F x) .barFive a
    rw [action_eq_multiplicity]
    simp [onMatter]

def onLight (F : Matter.Ten →ₗ[ℂ] Matter.Ten) : Light R →ₗ[ℂ] Light R :=
  (radicalEquiv R).symm.toLinearMap.comp
    ((onMatter F).comp (radicalEquiv R).toLinearMap)

def lightResidual : Representation ℂ H (Light R) :=
  (compatible R).action.comp (MonoidHom.inr GaugeGroup H)

theorem radical_residual (h : H) (x : Light R) :
    radicalEquiv R (lightResidual R h x) = residual R h (radicalEquiv R x) := by
  have he := (radicalEquiv R).toIntertwiningMap.isIntertwining _ _ (1, h) x
  simpa [lightResidual, smAction, joint, CommutingUnitaryActions.combined_apply] using he

theorem onLight_commutes (F : Matter.Ten →ₗ[ℂ] Matter.Ten) (h : H) (x : Light R) :
    onLight R F (lightResidual R h x) = lightResidual R h (onLight R F x) := by
  apply (radicalEquiv R).injective
  change radicalEquiv R ((radicalEquiv R).symm
    (onMatter F (radicalEquiv R (lightResidual R h x)))) =
    radicalEquiv R (lightResidual R h ((radicalEquiv R).symm
      (onMatter F (radicalEquiv R x))))
  rw [Representation.Equiv.apply_symm_apply, radical_residual, radical_residual,
    Representation.Equiv.apply_symm_apply]
  exact onMatter_commutes R F h _

def current (F : Matter.Ten →ₗ[ℂ] Matter.Ten) :
    Light R →ₗ[ℂ] Module.Dual ℂ (Module.Dual ℂ (Light R)) :=
  (Module.Dual.eval ℂ (Light R)).comp (onLight R F)

theorem current_invariant (F : Matter.Ten →ₗ[ℂ] Matter.Ten) (h : H)
    (x : Light R) (phi : Module.Dual ℂ (Light R)) :
    current R F (lightResidual R h x) ((lightResidual R).dual h phi) =
      current R F x phi := by
  change phi (lightResidual R h⁻¹ (onLight R F (lightResidual R h x))) = _
  rw [onLight_commutes]
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

def insertTen (a : Fin n) : Matter.Ten →ₗ[ℂ] Space n where
  toFun x := (gatherGenerations n).symm (Pi.single a (UnitaryMatter.tenEquiv x, 0))
  map_add' x y := by
    classical
    rw [← map_add]
    congr 1
    funext b
    by_cases h : b = a
    · subst b; simp
    · simp [h]
  map_smul' z x := by
    classical
    rw [← map_smul]
    congr 1
    funext b
    by_cases h : b = a
    · subst b; simp
    · simp [h]

def readTen (a : Fin n) : Space n →ₗ[ℂ] Matter.Ten where
  toFun x := UnitaryMatter.tenEquiv.symm (x .ten a)
  map_add' _ _ := map_add UnitaryMatter.tenEquiv.symm _ _
  map_smul' z _ := map_smul UnitaryMatter.tenEquiv.symm z _

theorem read_insert (a : Fin n) (x : Matter.Ten) : readTen a (insertTen a x) = x := by
  classical
  simp [readTen, insertTen, gatherGenerations]

theorem read_onMatter (a : Fin n) (F : Matter.Ten →ₗ[ℂ] Matter.Ten) (x : Space n) :
    readTen a (onMatter F x) = F (readTen a x) := by
  simp [readTen, onMatter, tenOperator]

def quark (a : Fin n) : StandardSMGaugeTensor.Quark →ₗ[ℂ] Light R :=
  (radicalEquiv R).symm.toLinearMap.comp ((insertTen a).comp quarkEmbed)

def observer (a : Fin n) (f : Module.Dual ℂ Matter.Ten) : Module.Dual ℂ (Light R) :=
  f.comp ((readTen a).comp (radicalEquiv R).toLinearMap)

def up (a : Fin n) (u : Color) : Module.Dual ℂ (Light R) :=
  observer R a ((Module.Dual.eval ℂ Color u).comp
    ((LinearMap.fst ℂ _ _).comp ExteriorSquareBranching.branch))

def electron (a : Fin n) (e : ℂ) : Module.Dual ℂ (Light R) :=
  observer R a ((Module.Dual.eval ℂ ℂ e).comp
    ((LinearMap.snd ℂ _ _).comp
      ((LinearMap.snd ℂ _ _).comp ExteriorSquareBranching.branch)))

theorem current_on_fields (a : Fin n) (F : Matter.Ten →ₗ[ℂ] Matter.Ten)
    (q : StandardSMGaugeTensor.Quark) (f : Module.Dual ℂ Matter.Ten) :
    current R F (quark R a q) (observer R a f) = f (F (quarkEmbed q)) := by
  change f (readTen a ((radicalEquiv R) (onLight R F (quark R a q)))) = _
  simp [onLight, quark, read_onMatter, read_insert]

theorem up_current (a : Fin n) (i : Fin 3) (w : Fin 2)
    (q : StandardSMGaugeTensor.Quark) (u : Color) :
    current R (infinitesimal (upper i w)) (quark R a q) (up R a u) = upCurrent i w q u :=
  current_on_fields R a _ q _

theorem electron_current (a : Fin n) (i : Fin 3) (w : Fin 2)
    (q : StandardSMGaugeTensor.Quark) (e : ℂ) :
    current R (infinitesimal (lower i w)) (quark R a q) (electron R a e) =
      electronCurrent i w q e := current_on_fields R a _ q _

theorem quark_injective (a : Fin n) : Function.Injective (quark R a) := by
  intro x y h
  have he := congrArg (fun z : Light R =>
    (ExteriorSquareBranching.branch (readTen a (radicalEquiv R z))).2.1) h
  simpa [quark, read_insert, branch_quarkEmbed] using he

private theorem branch_symm (x : ExteriorSquareBranching.Blocks) :
    ExteriorSquareBranching.branch (ExteriorSquareBranching.tenEquiv.symm x) = x :=
  ExteriorSquareBranching.tenEquiv.apply_symm_apply x

theorem up_injective (a : Fin n) : Function.Injective (up R a) := by
  intro x y h
  apply (Module.Free.chooseBasis ℂ Color).eval_injective
  apply LinearMap.ext
  intro f
  have he := congrArg (fun z : Module.Dual ℂ (Light R) =>
    z ((radicalEquiv R).symm (insertTen a
      (ExteriorSquareBranching.tenEquiv.symm (f, 0))))) h
  simpa [up, observer, read_insert, branch_symm] using he

theorem electron_injective (a : Fin n) : Function.Injective (electron R a) := by
  intro x y h
  have he := congrArg (fun z : Module.Dual ℂ (Light R) =>
    z ((radicalEquiv R).symm (insertTen a
      (ExteriorSquareBranching.tenEquiv.symm (0, (0, LinearMap.id)))))) h
  simpa [electron, observer, read_insert, branch_symm] using he

end
end GUT.SU5.LightRadical
