import GUT.SU6.SelectionRules.Models.AutomorphismCovariantModel
import Math.RepresentationTheory.Constructions.PointwiseInnerDefect

open Physics

/-! Actual-light-field tests for pointwise inner lifts in the unbroken group.
The hypotheses concern represented K-defects, not UV character support or
centrality alone. -/
namespace GUT.InnerDefectCandidate
set_option autoImplicit false
noncomputable section
open Math Representation AutomorphismCovariantModel PointwiseGaugeRemoval PointwiseInnerDefect
variable {H K : Type*} [CommGroup H] [TopologicalSpace H]
  [Group K] [TopologicalSpace K] (M : Model H K)
  (s : H → K) (hs : ∀ h g, M.beta h g = s h * g * (s h)⁻¹)

include hs

/-- A multiplication law on the actual radical iff its defect is invisible. -/
theorem light_mul_iff (h l : H) :
    removed M.mass.radical.toRepresentation M.beta (lightAction M) s h *
      removed M.mass.radical.toRepresentation M.beta (lightAction M) s l =
      removed M.mass.radical.toRepresentation M.beta (lightAction M) s (h * l) ↔
    M.mass.radical.toRepresentation (defect s h l) = 1 :=
  removed_mul_iff M.mass.radical.toRepresentation M.beta (lightAction M) s hs h l

/-- Conditional algebraic representation; no continuity certificate is inferred
for an arbitrary pointwise lift. -/
def lightRepresentation (h1 : s 1 = 1)
    (hd : ∀ h l, M.mass.radical.toRepresentation (defect s h l) = 1) :=
  removedRepresentation M.mass.radical.toRepresentation M.beta (lightAction M) s hs h1 hd

theorem lightRepresentation_commutes (h1 : s 1 = 1)
    (hd : ∀ h l, M.mass.radical.toRepresentation (defect s h l) = 1)
    (h : H) (g : K) :
    lightRepresentation M s hs h1 hd h * M.mass.radical.toRepresentation g =
      M.mass.radical.toRepresentation g * lightRepresentation M s hs h1 hd h :=
  removedRepresentation_commutes M.mass.radical.toRepresentation M.beta (lightAction M)
    s hs h1 hd h g
end
end GUT.InnerDefectCandidate
