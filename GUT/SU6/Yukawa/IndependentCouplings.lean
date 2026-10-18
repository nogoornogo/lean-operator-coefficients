import GUT.SU6.Yukawa.TwoBlockSpectrum
import GUT.SU6.SelectionRules.Models.StandardSMUVYukawa
import Physics.FieldTheory.Yukawa.ProjectedYukawa

open Math

/-! Independent full-SU(6) projected couplings and their exact light spectra. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6IndependentCouplings
noncomputable section
open Representation InvariantWeylMass WeylYukawaMass StandardSMUVFields
open StandardSMGaugeTensor (GaugeGroup)
attribute [local irreducible] ConcreteWeylBenchmark.matter

def baseYukawa : EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho :=
  StandardSMUVYukawa.yukawa

def exteriorProjection : IntertwiningMap uvRho uvRho where
  toLinearMap :=
    { toFun := fun x => ((x.1.1, 0), 0)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change ((ConcreteSU6Representations.exteriorTwo.rho g x.1.1, 0), 0) =
      ((ConcreteSU6Representations.exteriorTwo.rho g x.1.1,
        ConcreteSU6Representations.antifundamental.rho g 0),
        ConcreteSU6Representations.antifundamental.rho g 0)
    simp

def antiProjection : IntertwiningMap uvRho uvRho :=
  IntertwiningMap.id uvRho - exteriorProjection

theorem exterior_apply (x : UV) : exteriorProjection x = ((x.1.1, 0), 0) := rfl

theorem anti_apply (x : UV) : antiProjection x = ((0, x.1.2), x.2) := by
  change ((x.1.1, x.1.2), x.2) - ((x.1.1, 0), 0) = _
  apply Prod.ext
  · apply Prod.ext
    · exact sub_self _
    · exact sub_zero _
  · exact sub_zero _

theorem anti_eq_sub (x : UV) : antiProjection x = x - exteriorProjection x := rfl

def fiveCoupling := ProjectedYukawa.mixed baseYukawa
  exteriorProjection antiProjection
def singletCoupling := ProjectedYukawa.diagonal baseYukawa antiProjection
def coupling (a b : ℂ) := ProjectedYukawa.family baseYukawa
  exteriorProjection antiProjection a b

variable (H : Type*) [CommGroup H]

theorem baseYukawa_vacuum : baseYukawa.toLinearMap (StandardSMUVYukawa.vacuum H) =
    (StandardSMUVMass.mass H).form := StandardSMUVYukawa.vacuum_mass_form H

theorem residual_apply (x : UV) : withResidualEquiv H x = gaugeEquiv x := rfl

theorem reorder_apply (x : First) : reorderEquiv x = reorder x := rfl

theorem branch_apply (x : UV) : withResidualEquiv H x =
    (reorder (StandardSMExterior.analyticEquiv x.1.1,
      StandardSMContragredient.antifundamentalEquiv x.1.2),
      StandardSMGroup.analyticAntifundamentalEquiv x.2) := by
  rw [residual_apply, gaugeEquiv, SplitRepresentationProjection.prodEquiv_apply,
    Representation.Equiv.trans_apply, SplitRepresentationProjection.prodEquiv_apply,
    reorder_apply]

def fieldsProjection (x : StandardSMFullGaugeMass.Fields) : StandardSMFullGaugeMass.Fields :=
  (((x.1.1.1, (x.1.1.2.1, (0, (0, x.1.1.2.2.2.2)))),
    (x.1.2.1, (x.1.2.2.1, 0))), 0)

theorem projected_branch {A B C : Type*} [Zero B] [Zero C]
    (f : A → StandardSMExterior.Blocks)
    (g : B → (Module.Dual ℂ SMEpsilonTensor.Color ×
      (SMEpsilonTensor.Weak × Module.Dual ℂ ℂ)))
    (h : C → Module.Dual ℂ StandardSMFullGaugeMass.Heavy)
    (hg : g 0 = 0) (hh : h 0 = 0)
    (branch : (A × B) × C → StandardSMFullGaugeMass.Fields)
    (project : (A × B) × C → (A × B) × C)
    (hb : ∀ x, branch x = (reorder (f x.1.1, g x.1.2), h x.2))
    (hp : ∀ x, project x = ((x.1.1, 0), 0)) (x : (A × B) × C) :
    branch (project x) = fieldsProjection (branch x) := by
  rw [hp, hb, hb]
  simp only [hg, hh]
  simp [fieldsProjection, reorder]

theorem branch_projection (x : UV) :
    withResidualEquiv H (exteriorProjection x) = fieldsProjection (withResidualEquiv H x) := by
  exact projected_branch StandardSMExterior.analyticEquiv
    StandardSMContragredient.antifundamentalEquiv StandardSMGroup.analyticAntifundamentalEquiv
    (map_zero _) (map_zero _) (withResidualEquiv H) exteriorProjection (branch_apply H)
    exterior_apply x

theorem branch_anti (x : UV) : withResidualEquiv H (antiProjection x) =
    withResidualEquiv H x - fieldsProjection (withResidualEquiv H x) := by
  rw [anti_eq_sub, map_sub, branch_projection]

def mass (a b : ℂ) := ProjectedYukawa.familyMass baseYukawa
  exteriorProjection antiProjection
  (StandardSMGroup.withResidual H) (StandardSMUVYukawa.vacuum H)
  (StandardSMUVYukawa.vacuum_fixed H) a b

theorem transformed_form {V : Type*} (B : V → V → ℂ)
    (e : V → StandardSMFullGaugeMass.Fields) (p q : V → V)
    (hB : ∀ x y, B x y = (StandardSMFullGaugeMass.mass (neutralCharges H)).form (e x) (e y))
    (hp : ∀ x, e (p x) = fieldsProjection (e x))
    (hq : ∀ x, e (q x) = e x - fieldsProjection (e x))
    (a b : ℂ) (x y : V) :
    a * (B (p x) (q y) + B (q x) (p y)) + b * B (q x) (q y) =
      (SU6TwoBlockSpectrum.fieldsMass H a b).form (e x) (e y) := by
  rw [hB, hB, hB, hp, hp, hq, hq]
  generalize e x = X, e y = Y
  rw [SU6TwoBlockSpectrum.fieldsMass_apply]
  simp [StandardSMFullGaugeMass.mass, SplitWeylMass.mass,
    InvariantWeylMass.ofDirac, DiracWeylConvention.massBilinear,
    IntertwiningMap.snd, fieldsProjection, Prod.sub_def]

theorem transformed_mass_form {V : Type*} (B D : V → V → ℂ)
    (e : V → StandardSMFullGaugeMass.Fields) (p q : V → V)
    (hB : ∀ x y, B x y = (StandardSMFullGaugeMass.mass (neutralCharges H)).form (e x) (e y))
    (hp : ∀ x, e (p x) = fieldsProjection (e x))
    (hq : ∀ x, e (q x) = e x - fieldsProjection (e x))
    (a b : ℂ)
    (hD : ∀ x y, D x y = (SU6TwoBlockSpectrum.fieldsMass H a b).form (e x) (e y))
    (x y : V) : a * (B (p x) (q y) + B (q x) (p y)) + b * B (q x) (q y) = D x y :=
  (transformed_form H B e p q hB hp hq a b x y).trans (hD x y).symm

theorem transformed_bilinear {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (B D : LinearMap.BilinForm ℂ V) (e : V →ₗ[ℂ] StandardSMFullGaugeMass.Fields)
    (p q : V →ₗ[ℂ] V)
    (hB : B = (StandardSMFullGaugeMass.mass (neutralCharges H)).form.compl₁₂ e e)
    (hp : ∀ x, e (p x) = fieldsProjection (e x))
    (hq : ∀ x, e (q x) = e x - fieldsProjection (e x))
    (a b : ℂ)
    (hD : D = (SU6TwoBlockSpectrum.fieldsMass H a b).form.compl₁₂ e e) :
    ProjectedYukawa.projectedForm B p q a b = D := by
  ext x y
  change a * (B (p x) (q y) + B (q x) (p y)) + b * B (q x) (q y) = D x y
  exact transformed_mass_form H (fun x y => B x y) (fun x y => D x y) e p q
    (by intros; rw [hB]; rfl) hp hq a b (by intros; rw [hD]; rfl) x y

theorem original_pullback : (StandardSMUVMass.mass H).form =
    (StandardSMFullGaugeMass.mass (neutralCharges H)).form.compl₁₂
      (withResidualEquiv H).toLinearEquiv.toLinearMap
      (withResidualEquiv H).toLinearEquiv.toLinearMap := rfl

/-- Derive the complementary branching identity before specializing to the
analytic UV carrier, avoiding an expensive concrete coercion check. -/
theorem transformed_complement {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B D : LinearMap.BilinForm ℂ V) (e : V →ₗ[ℂ] StandardSMFullGaugeMass.Fields)
    (p q : V →ₗ[ℂ] V)
    (hB : B = (StandardSMFullGaugeMass.mass (neutralCharges H)).form.compl₁₂ e e)
    (hp : ∀ x, e (p x) = fieldsProjection (e x))
    (hq : ∀ x, q x = x - p x) (a b : ℂ)
    (hD : D = (SU6TwoBlockSpectrum.fieldsMass H a b).form.compl₁₂ e e) :
    ProjectedYukawa.projectedForm B p q a b = D := by
  apply transformed_bilinear H B D e p q hB hp _ a b hD
  intro x
  rw [hq, map_sub, hp]

theorem projected_mass_form (a b : ℂ) :
    ProjectedYukawa.projectedForm (StandardSMUVMass.mass H).form
      exteriorProjection.toLinearMap antiProjection.toLinearMap a b =
      (SU6TwoBlockSpectrum.mass H a b).form :=
  transformed_complement H (StandardSMUVMass.mass H).form
    (SU6TwoBlockSpectrum.massCertificate H a b).mass.form
    (withResidualEquiv H).toLinearEquiv.toLinearMap
    exteriorProjection.toLinearMap antiProjection.toLinearMap
    (original_pullback H) (branch_projection H) anti_eq_sub a b
    (SU6TwoBlockSpectrum.massCertificate H a b).form_eq

theorem mass_eq (a b : ℂ) : mass H a b = SU6TwoBlockSpectrum.mass H a b :=
  ProjectedYukawa.generated_mass_eq_from_form baseYukawa exteriorProjection antiProjection
    (StandardSMGroup.withResidual H) (StandardSMUVYukawa.vacuum H)
    (StandardSMUVYukawa.vacuum_fixed H) (StandardSMUVMass.mass H) (mass H a b)
    (SU6TwoBlockSpectrum.mass H a b)
    (baseYukawa_vacuum H) a b rfl (projected_mass_form H a b)

theorem radical_finrank (a b : ℂ) :
    Module.finrank ℂ (mass H a b).radical.toSubmodule =
      15 + (if a = 0 then 10 else 0) + (if b = 0 then 2 else 0) := by
  rw [mass_eq]
  exact SU6TwoBlockSpectrum.radical_finrank H a b

def fullRadicalEquiv (a b : ℂ) : Representation.Equiv (mass H a b).radical.toRepresentation
    ((StandardSMFullGaugeMass.lightRho (neutralCharges H)).prod
      (((OrthogonalMass.pair (SU6TwoBlockSpectrum.fiveRho H) a).radical.toRepresentation).prod
        (OrthogonalMass.pair (SU6TwoBlockSpectrum.singletRho H) b).radical.toRepresentation)) := by
  rw [mass_eq]
  exact SU6TwoBlockSpectrum.fullRadicalEquiv H a b

theorem mass_eq_iff (a b c d : ℂ) : mass H a b = mass H c d ↔ a = c ∧ b = d := by
  rw [mass_eq, mass_eq, SU6TwoBlockSpectrum.mass_eq_iff]

theorem fifteen (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.finrank ℂ (mass H a b).radical.toSubmodule = 15 := by
  simp [radical_finrank, ha, hb]

theorem seventeen (a : ℂ) (ha : a ≠ 0) :
    Module.finrank ℂ (mass H a 0).radical.toSubmodule = 17 := by
  simp [radical_finrank, ha]

theorem twentyFive (b : ℂ) (hb : b ≠ 0) :
    Module.finrank ℂ (mass H 0 b).radical.toSubmodule = 25 := by
  simp [radical_finrank, hb]

theorem twentySeven : Module.finrank ℂ (mass H 0 0).radical.toSubmodule = 27 := by
  simp [radical_finrank]

theorem coupling_eq_iff (a b c d : ℂ) : coupling a b = coupling c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    apply (mass_eq_iff Unit a b c d).mp
    exact ProjectedYukawa.familyMass_congr baseYukawa
      exteriorProjection antiProjection (StandardSMGroup.withResidual Unit)
      (StandardSMUVYukawa.vacuum Unit) (StandardSMUVYukawa.vacuum_fixed Unit) a b c d h
  · rintro ⟨rfl, rfl⟩
    rfl

end
end GUT.SU6IndependentCouplings
