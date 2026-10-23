import Physics.StandardModel.Operators.BaryonOne.Qque.FullLightSpeciesQque
import Physics.StandardModel.Operators.BaryonOne.Qque.MediatorQqueEvaluation

open Math

/-! Model obligations for a generated exchange on canonical full light
species. Nonzero exterior descent is derived from an alternating probe. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Physics.MediatorFullLightCertificate
noncomputable section
open Representation StandardSMGaugeTensor SMEpsilonTensor
open scoped TensorProduct

variable {H K V : Type*} [Group H]
  [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K]
  [AddCommGroup V] [Module ℂ V]
  (tau : Representation ℂ (GaugeGroup × H) K)

abbrev Q := (FullLightSpeciesQque.Q tau).toSubmodule
abbrev U := (FullLightSpeciesQque.U tau).toSubmodule
abbrev E := (FullLightSpeciesQque.E tau).toSubmodule
abbrev qRep := (FullLightSpeciesQque.Q tau).toRepresentation
abbrev uRep := (FullLightSpeciesQque.U tau).toRepresentation
abbrev eRep := (FullLightSpeciesQque.E tau).toRepresentation

variable (M : V ≃ₗ[ℂ] V) (g : ℂ)
  (J : Q tau ⊗[ℂ] U tau →ₗ[ℂ] V)
  (R : Q tau ⊗[ℂ] E tau →ₗ[ℂ] Module.Dual ℂ V)

structure Certificate where
  invariant : MediatorQque.IsInvariant (qRep tau) (uRep tau) (eRep tau) M g J R
  x : Q tau
  y : Q tau
  a : U tau
  b : E tau
  s : WeylSpinor.Space
  t : WeylSpinor.Space
  z : WeylSpinor.Space
  l : WeylSpinor.Space
  probe :
    MediatorExchange.coefficient M g J R ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) *
      (eps2 s t * eps2 z l) -
    MediatorExchange.coefficient M g J R ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) *
      (eps2 t s * eps2 z l) ≠ 0

namespace Certificate
variable {tau M g J R} (c : Certificate tau M g J R)

def generated : FullLightSpeciesQque.Sector tau :=
  MediatorQque.sector (qRep tau) (uRep tau) (eRep tau) M g J R c.invariant

omit [FiniteDimensional ℂ K] in
theorem generated_nonzero : c.generated ≠ 0 :=
  MediatorQqueEvaluation.sector_ne_zero_of_slots (qRep tau) (uRep tau) (eRep tau)
    M g J R c.invariant
    c.x c.y c.a c.b c.s c.t c.z c.l c.probe

variable (hs : IsSemisimpleRepresentation (ProductFactorization.firstRestriction tau))

def residualHom : FullLightSpeciesQque.ResidualHom tau :=
  (FullLightSpeciesQque.equiv tau hs).symm c.generated

theorem reconstruct : FullLightSpeciesQque.equiv tau hs (c.residualHom hs) = c.generated :=
  (FullLightSpeciesQque.equiv tau hs).apply_symm_apply c.generated

theorem residualHom_nonzero : c.residualHom hs ≠ 0 :=
  (FullLightSpeciesQque.equiv tau hs).symm.map_ne_zero_iff.mpr c.generated_nonzero

include c in
omit [FiniteDimensional ℂ K] in
theorem hasCoefficient : FullLightSpeciesQque.HasCoefficient tau :=
  ⟨c.generated, c.generated_nonzero⟩

include c hs in
theorem hasResidualMap : FullLightSpeciesQque.HasResidualMap tau :=
  ⟨c.residualHom hs, c.residualHom_nonzero hs⟩

end Certificate

def ofRestriction
    {A B C : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    (h : MediatorQque.IsInvariant (qRep tau) (uRep tau) (eRep tau) M g J R)
    (iQ : A →ₗ[ℂ] Q tau) (iU : B →ₗ[ℂ] U tau) (iE : C →ₗ[ℂ] E tau)
    (f : (A ⊗[ℂ] A) ⊗[ℂ] (B ⊗[ℂ] C) →ₗ[ℂ] ℂ)
    (hf : ∀ x y a b, MediatorExchange.coefficient M g J R
      ((iQ x ⊗ₜ[ℂ] iQ y) ⊗ₜ[ℂ] (iU a ⊗ₜ[ℂ] iE b)) =
        f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)))
    (x y : A) (a : B) (b : C) (s t z l : WeylSpinor.Space)
    (hn : f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) * (eps2 s t * eps2 z l) -
      f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) * (eps2 t s * eps2 z l) ≠ 0) :
    Certificate tau M g J R where
  invariant := h
  x := iQ x
  y := iQ y
  a := iU a
  b := iE b
  s := s
  t := t
  z := z
  l := l
  probe := by simpa only [hf] using hn

end
end Physics.MediatorFullLightCertificate
