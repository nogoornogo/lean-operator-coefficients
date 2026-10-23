import GUT.SU6.SelectionRules.Models.AutomorphismCovariantModel
import Math.RepresentationTheory.Exterior.AutomorphismCovariantExterior

open Physics

/-! Degree-four exterior coefficient interface on actual SU(6) light fields.
This gauge/residual interface alone is not a full Lorentz operator theorem. -/
namespace GUT.CovariantFourFermion
set_option autoImplicit false
noncomputable section
open Math Representation AutomorphismCovariantModel

variable {H K : Type*} [CommGroup H] [TopologicalSpace H]
  [Group K] [TopologicalSpace K] (M : Model H K)

abbrev Support := AutomorphismCovariantExterior.Support
  M.mass.radical.toRepresentation M.beta (lightAction M) 4

variable (S : Support M)

/-- Exterior action is derived on actual radical vectors; it is not an input. -/
def exteriorAction := AutomorphismCovariantExterior.exteriorAction
  M.mass.radical.toRepresentation M.beta (lightAction M) 4

/-- Complete supported gauge/residual four-field coefficients. Lorentz and the
physical BNV dictionary must be supplied before interpreting this as dimension six. -/
def equiv := AutomorphismCovariantExterior.equiv
  M.mass.radical.toRepresentation M.beta (lightAction M) S

abbrev Residual := IntertwiningMap
  (AutomorphismCovariantHom.quotient
    (AutomorphismCovariantExterior.localQuotient
      M.mass.radical.toRepresentation M.beta (lightAction M) S)
    M.beta (AutomorphismCovariantExterior.supportedAction
      M.mass.radical.toRepresentation M.beta (lightAction M) S))
  (trivial ℂ H ℂ)

theorem forbidden_iff :
    (∀ f : LocalCoinvariantHom.invariantHom
      (AutomorphismCovariantExterior.localQuotient
        M.mass.radical.toRepresentation M.beta (lightAction M) S)
      (AutomorphismCovariantExterior.supportedAction
        M.mass.radical.toRepresentation M.beta (lightAction M) S).residual
      (trivial ℂ H ℂ), f = 0) ↔ ∀ q : Residual M S, q = 0 := AutomorphismCovariantExterior.forbidden_iff
  M.mass.radical.toRepresentation M.beta (lightAction M) S

/-- Original supported functionals on the fourth exterior power of light fields. -/
abbrev Input := AutomorphismCovariantExterior.Input
  M.mass.radical.toRepresentation M.beta (lightAction M) S

def inputEquiv := AutomorphismCovariantExterior.inputEquiv
  M.mass.radical.toRepresentation M.beta (lightAction M) S

theorem input_forbidden_iff : (∀ f : Input M S, f = 0) ↔
    ∀ q : Residual M S, q = 0 := AutomorphismCovariantExterior.input_forbidden_iff
  M.mass.radical.toRepresentation M.beta (lightAction M) S

end
end GUT.CovariantFourFermion
