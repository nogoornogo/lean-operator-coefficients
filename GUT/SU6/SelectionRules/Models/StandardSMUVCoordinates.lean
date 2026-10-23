import GUT.SU6.SelectionRules.Models.StandardSMUVMass

open Physics

open Math

/-!
# Coordinate access to the existing UV branching equivalences

Changing a representation by a proved equality does not change its underlying
linear equivalence. These lemmas expose the existing maps without changing the
mass or any representation. Keeping the coercion steps separate also avoids
expanding the analytic unitarization during kernel checking.
-/

set_option autoImplicit false

namespace GUT.StandardSMUVCoordinates

noncomputable section

open StandardSMUVFields SplitRepresentationProjection

private theorem source_cast_linear {G V W : Type*} [Monoid G]
    [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    {rho tau : Representation ℂ G V} (h : rho = tau)
    (sigma : Representation ℂ G W) (e : Representation.Equiv tau sigma) :
    ((congrArg (fun r => Representation.Equiv r sigma) h).mpr e).toLinearEquiv =
      e.toLinearEquiv := by
  cases h
  rfl

theorem equiv_apply {R G V W : Type*} [s : Semiring R] [Monoid G]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    {rho : Representation R G V} {sigma : Representation R G W}
    (e : Representation.Equiv rho sigma) (x : V) : e x = e.toLinearEquiv x := rfl

theorem withResidualEquiv_linear (H : Type*) [CommGroup H] :
    (withResidualEquiv H).toLinearEquiv = gaugeEquiv.toLinearEquiv := rfl

theorem withResidualEquiv_apply (H : Type*) [CommGroup H] (x : UV) :
    withResidualEquiv H x = gaugeEquiv x := by
  rw [equiv_apply, equiv_apply, withResidualEquiv_linear]

private theorem anti_eq : StandardSMGroup.antifundamentalEquiv =
    (congrArg (fun r => Representation.Equiv r StandardSMGroup.heavy.dual)
      (dual_comp FundamentalRepresentation.rho StandardSMGroup.hom)).mpr
      (dualEquiv StandardSMGroup.fundamentalEquiv) := rfl

attribute [local irreducible] StandardSMGroup.hom FundamentalRepresentation.rho

private theorem anti_cast_linear
    (e : Representation.Equiv (Representation.dual (FundamentalRepresentation.rho.comp StandardSMGroup.hom))
      StandardSMGroup.heavy.dual) :
    ((congrArg (fun r => Representation.Equiv r StandardSMGroup.heavy.dual)
      (dual_comp FundamentalRepresentation.rho StandardSMGroup.hom)).mpr e).toLinearEquiv =
      e.toLinearEquiv :=
  source_cast_linear
    (rho := FundamentalRepresentation.rho.dual.comp StandardSMGroup.hom)
    (tau := Representation.dual (FundamentalRepresentation.rho.comp StandardSMGroup.hom))
    (dual_comp FundamentalRepresentation.rho StandardSMGroup.hom)
    StandardSMGroup.heavy.dual e

private theorem anti_linear : StandardSMGroup.antifundamentalEquiv.toLinearEquiv =
    (dualEquiv StandardSMGroup.fundamentalEquiv).toLinearEquiv := by
  rw [anti_eq]
  exact anti_cast_linear (dualEquiv StandardSMGroup.fundamentalEquiv)

private theorem dual_fundamental_linear :
    (dualEquiv StandardSMGroup.fundamentalEquiv).toLinearEquiv =
      StandardSMGroup.splitEquiv.symm.dualMap := rfl

theorem antifundamentalEquiv_linear : StandardSMGroup.antifundamentalEquiv.toLinearEquiv =
    StandardSMGroup.splitEquiv.symm.dualMap := anti_linear.trans dual_fundamental_linear

theorem trans_linear {G V W X : Type*} [Monoid G]
    [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    [AddCommMonoid X] [Module ℂ X]
    {rho : Representation ℂ G V} {sigma : Representation ℂ G W}
    {tau : Representation ℂ G X} (e : Representation.Equiv rho sigma)
    (f : Representation.Equiv sigma tau) :
    (e.trans f).toLinearEquiv = e.toLinearEquiv.trans f.toLinearEquiv := rfl

private theorem restrict_linear {G K V W : Type*} [Group G] [Group K]
    [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    {rho : Representation ℂ G V} {sigma : Representation ℂ G W}
    (e : Representation.Equiv rho sigma) (f : K →* G) :
    (restrictEquiv e f).toLinearEquiv = e.toLinearEquiv := rfl

theorem antifundamentalEquiv_apply (phi : Module.Dual ℂ (Fin 6 → ℂ))
    (x : StandardSMFullGaugeMass.Heavy) :
    StandardSMGroup.antifundamentalEquiv phi x = phi (StandardSMGroup.splitEquiv.symm x) := by
  rw [equiv_apply (s := Complex.instCommSemiring.toSemiring),
    antifundamentalEquiv_linear, LinearEquiv.dualMap_apply]

theorem analyticAntifundamentalEquiv_linear :
    StandardSMGroup.analyticAntifundamentalEquiv.toLinearEquiv =
      ConcreteSU6Representations.antifundamentalEquiv.symm.toLinearEquiv.trans
        StandardSMGroup.splitEquiv.symm.dualMap := by
  unfold StandardSMGroup.analyticAntifundamentalEquiv
  erw [trans_linear, restrict_linear, antifundamentalEquiv_linear]

theorem prod_linear {G V W X Y : Type*} [Group G]
    [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    {rho : Representation ℂ G V} {sigma : Representation ℂ G W}
    {tau : Representation ℂ G X} {omega : Representation ℂ G Y}
    (e : Representation.Equiv rho sigma) (f : Representation.Equiv tau omega) :
    (prodEquiv e f).toLinearEquiv = e.toLinearEquiv.prodCongr f.toLinearEquiv := rfl

private theorem pullback_form {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {rho : Representation ℂ G V} {sigma : Representation ℂ G W}
    (e : Representation.Equiv rho sigma) (B : InvariantWeylMass.SymmetricMass sigma) :
    (EquivariantWeylMassTransport.pullback e B).form =
      B.form.compl₁₂ e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap := rfl

attribute [local irreducible] uvRho

theorem mass_form_gauge (H : Type*) [CommGroup H] :
    (StandardSMUVMass.mass H).form =
      (StandardSMFullGaugeMass.mass (neutralCharges H)).form.compl₁₂
        gaugeEquiv.toLinearEquiv.toLinearMap gaugeEquiv.toLinearEquiv.toLinearMap := by
  rw [StandardSMUVMass.mass_form_eq]
  erw [pullback_form]
  exact congrArg (fun e : UV ≃ₗ[ℂ] StandardSMFullGaugeMass.Fields =>
    (StandardSMFullGaugeMass.mass (neutralCharges H)).form.compl₁₂ e.toLinearMap e.toLinearMap)
    (withResidualEquiv_linear H)

end

end GUT.StandardSMUVCoordinates
