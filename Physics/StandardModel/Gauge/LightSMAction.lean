import Physics.StandardModel.Gauge.CompactExplicitSMTensor
import TauCeti.Topology.Algebra.UnitaryGroup

open Math

/-! A compatible SM action on the original mass radical. Preservation of
the radical suffices; invariance of the whole mass is a separate constructor. -/

namespace GUT.LightSMAction
set_option autoImplicit false
noncomputable section

open Representation InvariantWeylMass ContinuousRepresentationScope
open SU5.MaximalTorus

variable {H G E : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))

/-- This input does not specify particle subspaces, splittings or a tensor. -/
structure Compatible where
  action : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) B.radical.toSubmodule
  restriction : action.comp (SU5.PhysicalTorus.gaugeHom.prodMap (MonoidHom.id H)) =
    B.radical.toRepresentation.comp (SU5.PhysicalTorus.toTorus.prodMap (MonoidHom.id H))

theorem residual_agrees (D : Compatible j rho B) (h : H) :
    D.action (1, h) = B.radical.toRepresentation (1, h) := by
  have he := DFunLike.congr_fun D.restriction (1, h)
  simpa using he

theorem residual_restriction (D : Compatible j rho B) :
    D.action.comp (MonoidHom.inr _ H) =
      B.radical.toRepresentation.comp (MonoidHom.inr _ H) := by
  apply MonoidHom.ext
  exact residual_agrees j rho B D

theorem dual_restriction (D : Compatible j rho B) :
    D.action.dual.comp (SU5.PhysicalTorus.gaugeHom.prodMap (MonoidHom.id H)) =
      B.radical.toRepresentation.dual.comp
        (SU5.PhysicalTorus.toTorus.prodMap (MonoidHom.id H)) := by
  rw [SplitRepresentationProjection.dual_comp, D.restriction,
    SplitRepresentationProjection.dual_comp]

theorem dual_residual_restriction (D : Compatible j rho B) :
    D.action.dual.comp (MonoidHom.inr _ H) =
      B.radical.toRepresentation.dual.comp (MonoidHom.inr _ H) := by
  rw [SplitRepresentationProjection.dual_comp, residual_restriction,
    SplitRepresentationProjection.dual_comp]

def ofDecomposition (D : CompactExplicitSMTensor.Decomposition j rho B) :
    Compatible j rho B := ⟨D.action, D.restriction⟩

variable (gamma : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) E)

def PreservesRadical : Prop := ∀ g x, x ∈ B.radical.toSubmodule →
  gamma g x ∈ B.radical.toSubmodule

def radicalSubrepresentation (hp : PreservesRadical j rho B gamma) :
    Subrepresentation gamma where
  toSubmodule := B.radical.toSubmodule
  apply_mem_toSubmodule g _ hx := hp g _ hx

def ofPreservesRadical (hp : PreservesRadical j rho B gamma)
    (hc : gamma.comp (SU5.PhysicalTorus.gaugeHom.prodMap (MonoidHom.id H)) =
      (rho.comp (j.prodMap (MonoidHom.id H))).comp
        (SU5.PhysicalTorus.toTorus.prodMap (MonoidHom.id H))) :
    Compatible j rho B where
  action := (radicalSubrepresentation j rho B gamma hp).toRepresentation
  restriction := by
    ext g x
    exact LinearMap.congr_fun (DFunLike.congr_fun hc g) x.val

@[simp] theorem ofPreservesRadical_apply
    (hp : PreservesRadical j rho B gamma)
    (hc : gamma.comp (SU5.PhysicalTorus.gaugeHom.prodMap (MonoidHom.id H)) =
      (rho.comp (j.prodMap (MonoidHom.id H))).comp
        (SU5.PhysicalTorus.toTorus.prodMap (MonoidHom.id H)))
    (g : StandardSMGaugeTensor.GaugeGroup × H) (x : B.radical.toSubmodule) :
    ((ofPreservesRadical j rho B gamma hp hc).action g x).val = gamma g x.val := rfl

def massForAction
    (hb : ∀ g x y, B.form (gamma g x) (gamma g y) = B.form x y) :
    SymmetricMass gamma where
  form := B.form
  symmetric := B.symmetric
  invariant := hb

@[simp] theorem massForAction_form
    (hb : ∀ g x y, B.form (gamma g x) (gamma g y) = B.form x y) :
    (massForAction j rho B gamma hb).form = B.form := rfl

@[simp] theorem massForAction_radical
    (hb : ∀ g x y, B.form (gamma g x) (gamma g y) = B.form x y) :
    (massForAction j rho B gamma hb).radical.toSubmodule = B.radical.toSubmodule := rfl

theorem preservesRadical_of_invariant
    (hb : ∀ g x y, B.form (gamma g x) (gamma g y) = B.form x y) :
    PreservesRadical j rho B gamma := by
  intro g x hx
  exact (massForAction j rho B gamma hb).radical.apply_mem_toSubmodule g hx

def ofInvariantMass
    (hb : ∀ g x y, B.form (gamma g x) (gamma g y) = B.form x y)
    (hc : gamma.comp (SU5.PhysicalTorus.gaugeHom.prodMap (MonoidHom.id H)) =
      (rho.comp (j.prodMap (MonoidHom.id H))).comp
        (SU5.PhysicalTorus.toTorus.prodMap (MonoidHom.id H))) :
    Compatible j rho B :=
  ofPreservesRadical j rho B gamma (preservesRadical_of_invariant j rho B gamma hb) hc

variable [TopologicalSpace H]

theorem ofPreservesRadical_continuous
    (hp : PreservesRadical j rho B gamma)
    (hc : gamma.comp (SU5.PhysicalTorus.gaugeHom.prodMap (MonoidHom.id H)) =
      (rho.comp (j.prodMap (MonoidHom.id H))).comp
        (SU5.PhysicalTorus.toTorus.prodMap (MonoidHom.id H)))
    (hg : IsJointlyContinuous gamma) :
    IsJointlyContinuous (ofPreservesRadical j rho B gamma hp hc).action :=
  hg.subrepresentation (radicalSubrepresentation j rho B gamma hp)

theorem ofInvariantMass_continuous
    (hb : ∀ g x y, B.form (gamma g x) (gamma g y) = B.form x y)
    (hc : gamma.comp (SU5.PhysicalTorus.gaugeHom.prodMap (MonoidHom.id H)) =
      (rho.comp (j.prodMap (MonoidHom.id H))).comp
        (SU5.PhysicalTorus.toTorus.prodMap (MonoidHom.id H)))
    (hg : IsJointlyContinuous gamma) :
    IsJointlyContinuous (ofInvariantMass j rho B gamma hb hc).action :=
  ofPreservesRadical_continuous j rho B gamma
    (preservesRadical_of_invariant j rho B gamma hb) hc hg

variable [IsTopologicalGroup H] [FiniteDimensional ℂ E]

theorem dual_continuous (D : Compatible j rho B) (hd : IsJointlyContinuous D.action) :
    letI := ContinuousDual.dualNormedAddCommGroup (V := B.radical.toSubmodule)
    letI := ContinuousDual.dualNormedSpace (V := B.radical.toSubmodule)
    IsJointlyContinuous D.action.dual :=
  ContinuousDual.jointlyContinuous_dual D.action hd

end
end GUT.LightSMAction
