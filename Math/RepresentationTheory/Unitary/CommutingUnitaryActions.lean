import Math.RepresentationTheory.Multiplicity.UnitaryMultiplicity
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Analysis.Complex.Circle
import Mathlib.RepresentationTheory.Character

/-! Strict commuting actions are exactly the data needed for the product
action. No scalar action, residual finiteness, or continuity is inferred. -/

set_option autoImplicit false

namespace Math.CommutingUnitaryActions

noncomputable section

variable {G H E : Type*} [Group G] [Group H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (rho : Representation ℂ G E) (alpha : Representation ℂ H E)
  (hc : ∀ g h, Commute (rho g) (alpha h))

def combined : Representation ℂ (G × H) E := rho.noncommCoprod alpha hc

@[simp] theorem combined_apply (g : G) (h : H) (v : E) :
    combined rho alpha hc (g, h) v = rho g (alpha h v) := rfl

theorem combined_unitary
    (hr : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (ha : UnitaryMultiplicity.IsUnitaryRepresentation alpha) :
    UnitaryMultiplicity.IsUnitaryRepresentation (combined rho alpha hc) := by
  intro g v w
  change inner ℂ (rho g.1 (alpha g.2 v)) (rho g.1 (alpha g.2 w)) = inner ℂ v w
  rw [hr, ha]

theorem combined_restrict_left :
    (combined rho alpha hc).comp (MonoidHom.inl G H) = rho :=
  MonoidHom.noncommCoprod_comp_inl rho alpha hc

theorem combined_restrict_right :
    (combined rho alpha hc).comp (MonoidHom.inr G H) = alpha :=
  MonoidHom.noncommCoprod_comp_inr rho alpha hc

theorem combined_jointlyContinuous [TopologicalSpace G] [TopologicalSpace H]
    (hr : Continuous (fun p : G × E => rho p.1 p.2))
    (ha : Continuous (fun p : H × E => alpha p.1 p.2)) :
    Continuous (fun p : (G × H) × E => combined rho alpha hc p.1 p.2) :=
  hr.comp ((continuous_fst.comp continuous_fst).prodMk
    (ha.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))

def charged (chi : H →* Circle) : Representation ℂ (G × H) E where
  toFun g := (chi g.2 : ℂ) • rho g.1
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

theorem charged_unitary (chi : H →* Circle)
    (hr : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    UnitaryMultiplicity.IsUnitaryRepresentation (charged rho chi) := by
  intro g x y
  change inner ℂ ((chi g.2 : ℂ) • rho g.1 x) ((chi g.2 : ℂ) • rho g.1 y) = _
  rw [inner_smul_left, inner_smul_right, hr, ← mul_assoc, ← Circle.coe_inv_eq_conj,
    ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_mul]

theorem charged_character [FiniteDimensional ℂ E] (chi : H →* Circle) (g : G × H) :
    (charged rho chi).character g = (chi g.2 : ℂ) * rho.character g.1 := by
  change LinearMap.trace ℂ E ((chi g.2 : ℂ) • rho g.1) = _
  rw [map_smul]
  rfl

theorem charged_jointlyContinuous [TopologicalSpace G] [TopologicalSpace H]
    (chi : H →* Circle) (hc : Continuous chi)
    (hr : Continuous (fun p : G × E => rho p.1 p.2)) :
    Continuous (fun p : (G × H) × E => charged rho chi p.1 p.2) :=
  ((continuous_subtype_val.comp hc).comp (continuous_snd.comp continuous_fst)).smul
    (hr.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))

end

end Math.CommutingUnitaryActions
