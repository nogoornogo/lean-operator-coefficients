import GUT.SU5.Matching.LightSpeciesExhaustion
import Math.LinearAlgebra.FourSlotGeneration

open Math

/-! Restrict the previous exchange, with its actual currents, to all standard
Q/up/e species. No coefficient equality or invariance is an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU5.LightSpeciesExchange
noncomputable section
open Representation MatterSource LightRadical LightSpeciesMaps LightSpeciesExhaustion
open GeorgiGlashowSource StandardSMGaugeTensor SMEpsilonTensor HeavyCurrents
open ExteriorSquareCoordinates (infinitesimal)
open scoped TensorProduct
variable {H : Type*} [Group H] {n : ℕ} (R : OrdinaryAction H n)

abbrev qRep := (FullLightSpeciesQque.Q (tau R)).toRepresentation
abbrev uRep := (FullLightSpeciesQque.U (tau R)).toRepresentation
abbrev eRep := (FullLightSpeciesQque.E (tau R)).toRepresentation
abbrev QSpace := (FullLightSpeciesQque.Q (tau R)).toSubmodule
abbrev USpace := (FullLightSpeciesQque.U (tau R)).toSubmodule
abbrev ESpace := (FullLightSpeciesQque.E (tau R)).toSubmodule

local instance : AddCommGroup (QSpace R) := inferInstance
local instance : Module ℂ (QSpace R) := inferInstance
local instance : AddCommGroup (USpace R) := inferInstance
local instance : Module ℂ (USpace R) := inferInstance
local instance : AddCommGroup (ESpace R) := inferInstance
local instance : Module ℂ (ESpace R) := inferInstance
local instance : AddCommGroup Quark := inferInstance

def leftCurrent : QSpace R ⊗[ℂ] USpace R →ₗ[ℂ] MediatorMatching.Channels :=
  (LightRadicalExchange.leftCurrent R).comp
    (TensorProduct.map (QSpace R).subtype (USpace R).subtype)
def rightCurrent : QSpace R ⊗[ℂ] ESpace R →ₗ[ℂ] Module.Dual ℂ MediatorMatching.Channels :=
  (LightRadicalExchange.rightCurrent R).comp
    (TensorProduct.map (QSpace R).subtype (ESpace R).subtype)

def coefficient (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :=
  MediatorExchange.coefficient (MediatorMatching.mass g v hg hv) (g : ℂ)
    (leftCurrent R) (rightCurrent R)

theorem coefficient_restrict (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0)
    (q s : QSpace R) (u : USpace R) (e : ESpace R) :
    coefficient R g v hg hv ((q ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) =
    LightRadicalExchange.coefficient R g v hg hv
      ((q.val ⊗ₜ[ℂ] s.val) ⊗ₜ[ℂ] (u.val ⊗ₜ[ℂ] e.val)) := rfl

theorem current_cross (a b : Fin n) (F : Matter.Ten →ₗ[ℂ] Matter.Ten)
    (q : Quark) (f : Module.Dual ℂ Matter.Ten) :
    current R F (LightRadical.quark R a q) (observer R b f) =
      if a = b then f (F (quarkEmbed q)) else 0 := by
  classical
  change f (readTen b (radicalEquiv R (onLight R F (LightRadical.quark R a q)))) = _
  change f (readTen b (radicalEquiv R ((radicalEquiv R).symm
    (onMatter F (radicalEquiv R ((radicalEquiv R).symm (insertTen a (quarkEmbed q)))))))) = _
  rw [Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply,
    read_onMatter, read_insert_cross]
  by_cases h : a = b
  · subst b; simp
  · simp [h, Ne.symm h]

theorem left_cross (a b : Fin n) (q : Quark) (u : Color) :
    leftCurrent R (Q R a q ⊗ₜ[ℂ] U R b u) =
      if a = b then MediatorMatching.leftCurrent (q ⊗ₜ[ℂ] u) else 0 := by
  classical
  funext i w
  change current R (infinitesimal (upper i w)) (LightRadical.quark R a q) (up R b u) = _
  rw [up, current_cross]
  split_ifs <;> rfl

theorem right_cross (a b : Fin n) (q : Quark) (e : ℂ) :
    rightCurrent R (Q R a q ⊗ₜ[ℂ] E R b e) =
      if a = b then MediatorMatching.rightCurrent (q ⊗ₜ[ℂ] e) else 0 := by
  classical
  have he : (fun i w => current R (infinitesimal (lower i w))
      (LightRadical.quark R a q) (electron R b e)) =
      if a = b then (fun i w => electronCurrent i w q e) else 0 := by
    funext i w
    rw [electron, current_cross]
    split_ifs <;> rfl
  refine (congrArg MediatorMatching.pairing he).trans ?_
  split_ifs
  · rfl
  · exact map_zero _

theorem coefficient_generations (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0)
    (a b c d : Fin n) (q s : Quark) (u : Color) (e : ℂ) :
    coefficient R g v hg hv ((Q R a q ⊗ₜ[ℂ] Q R b s) ⊗ₜ[ℂ]
      (U R c u ⊗ₜ[ℂ] E R d e)) =
    if a = c ∧ b = d then
      MediatorMatching.coefficient g v hg hv ((q ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) else 0 := by
  classical
  simp only [coefficient, MediatorExchange.coefficient_tmul, left_cross, right_cross]
  by_cases h : a = c <;> by_cases k : b = d <;>
    simp [h, k, MediatorMatching.coefficient, MediatorExchange.coefficient_tmul]

theorem Q_action (g : GaugeGroup) (a : Fin n) (q : Quark) :
    qRep R (g, 1) (Q R a q) = Q R a (StandardSMGaugeTensor.quark g q) := by
  apply Subtype.ext
  exact ((quarkSM R a).isIntertwining _ _ g q).symm
theorem U_action (g : GaugeGroup) (a : Fin n) (u : Color) :
    uRep R (g, 1) (U R a u) = U R a (upRight g u) := by
  apply Subtype.ext
  exact ((upSM R a).isIntertwining _ _ g u).symm
theorem E_action (g : GaugeGroup) (a : Fin n) (e : ℂ) :
    eRep R (g, 1) (E R a e) = E R a (electronRight g e) := by
  apply Subtype.ext
  exact ((electronSM R a).isIntertwining _ _ g e).symm

theorem generations_sm (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (s : GaugeGroup)
    (a b c d : Fin n) (x y : Quark) (u : Color) (e : ℂ) :
    coefficient R g v hg hv
      ((Q R a (StandardSMGaugeTensor.quark s x) ⊗ₜ[ℂ] Q R b (StandardSMGaugeTensor.quark s y)) ⊗ₜ[ℂ]
        (U R c (upRight s u) ⊗ₜ[ℂ] E R d (electronRight s e))) =
    coefficient R g v hg hv ((Q R a x ⊗ₜ[ℂ] Q R b y) ⊗ₜ[ℂ] (U R c u ⊗ₜ[ℂ] E R d e)) := by
  refine (coefficient_generations R g v hg hv a b c d
    (StandardSMGaugeTensor.quark s x) (StandardSMGaugeTensor.quark s y)
    (upRight s u) (electronRight s e)).trans ?_
  refine Eq.trans ?_ (coefficient_generations R g v hg hv a b c d x y u e).symm
  split_ifs
  · exact MediatorMatching.invariant g v hg hv s ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e))
  · rfl

theorem sm_invariant (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (s : GaugeGroup)
    (x y : QSpace R) (u : USpace R) (e : ESpace R) :
    coefficient R g v hg hv
      ((qRep R (s, 1) x ⊗ₜ[ℂ] qRep R (s, 1) y) ⊗ₜ[ℂ]
        (uRep R (s, 1) u ⊗ₜ[ℂ] eRep R (s, 1) e)) =
    coefficient R g v hg hv ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  have he : (coefficient R g v hg hv).comp
      (((qRep R).tprod (qRep R)).tprod ((uRep R).tprod (eRep R)) (s, 1)) =
        coefficient R g v hg hv := by
    apply FourSlotGeneration.ext (Q R) (U R) (E R)
      (allQ_surjective R) (allU_surjective R) (allE_surjective R)
    intro a b c d xx yy uu ee
    change coefficient R g v hg hv
      ((qRep R (s, 1) (Q R a xx) ⊗ₜ[ℂ] qRep R (s, 1) (Q R b yy)) ⊗ₜ[ℂ]
        (uRep R (s, 1) (U R c uu) ⊗ₜ[ℂ] eRep R (s, 1) (E R d ee))) = _
    simp only [Q_action, U_action, E_action]
    exact generations_sm R g v hg hv s a b c d xx yy uu ee
  exact DFunLike.congr_fun he ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e))

theorem Q_h_action (h : H) (x : QSpace R) :
    (qRep R (1, h) x).val = lightResidual R h x.val := rfl

theorem U_h_action (h : H) (u : USpace R) :
    (uRep R (1, h) u).val = (lightResidual R).dual h u.val := by
  apply LinearMap.ext
  intro x
  change u.val (tau R ((1, h)⁻¹) x) = u.val (tau R (1, h⁻¹) x)
  simp only [Prod.inv_mk, inv_one]

theorem E_h_action (h : H) (e : ESpace R) :
    (eRep R (1, h) e).val = (lightResidual R).dual h e.val := by
  apply LinearMap.ext
  intro x
  change e.val (tau R ((1, h)⁻¹) x) = e.val (tau R (1, h⁻¹) x)
  simp only [Prod.inv_mk, inv_one]

theorem h_invariant (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (h : H)
    (x y : QSpace R) (u : USpace R) (e : ESpace R) :
    coefficient R g v hg hv
      ((qRep R (1, h) x ⊗ₜ[ℂ] qRep R (1, h) y) ⊗ₜ[ℂ]
        (uRep R (1, h) u ⊗ₜ[ℂ] eRep R (1, h) e)) =
    coefficient R g v hg hv ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  simp only [coefficient_restrict, Q_h_action, U_h_action, E_h_action,
    LightRadicalExchange.coefficient, MediatorExchange.coefficient_tmul,
    LightRadicalExchange.left_invariant, LightRadicalExchange.right_invariant]

theorem invariant (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    MediatorQque.IsInvariant (qRep R) (uRep R) (eRep R)
      (MediatorMatching.mass g v hg hv) (g : ℂ) (leftCurrent R) (rightCurrent R) := by
  intro p z
  have he : (coefficient R g v hg hv).comp
      (((qRep R).tprod (qRep R)).tprod ((uRep R).tprod (eRep R)) p) = coefficient R g v hg hv := by
    apply TensorProduct.ext_fourfold'
    intro x y u e
    change coefficient R g v hg hv
      ((qRep R p x ⊗ₜ[ℂ] qRep R p y) ⊗ₜ[ℂ] (uRep R p u ⊗ₜ[ℂ] eRep R p e)) = _
    have hp : p = (p.1, 1) * (1, p.2) := by simp
    conv_lhs => rw [hp]
    simp only [map_mul, Module.End.mul_apply]
    exact (sm_invariant R g v hg hv p.1 _ _ _ _).trans
      (h_invariant R g v hg hv p.2 x y u e)
  exact DFunLike.congr_fun he z

end
end GUT.SU5.LightSpeciesExchange
