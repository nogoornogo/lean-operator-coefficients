import Math.LieGroups.E6.Minuscule.TorusFundamentalGroup
import Math.LieGroups.E6.Minuscule.TorusCentralizer
import Math.LieGroups.E6.Minuscule.CompactPathConnected
import Math.Topology.MaximalTorusFundamentalGroup

/-!
# Conditional candidate simple connectedness from a literature input

Every theorem below retains `hLiterature` explicitly. No value of that input
is supplied. The former unproved L5-L8 chain is not imported. The torus itself
is not simply connected: it is its induced map into the candidate that is trivial.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open scoped Manifold Matrix.Norms.L2Operator ContDiff

namespace Torus

/-- The actual six-circle inclusion satisfies the external theorem's torus inputs. -/
def maximalTorusData : Math.Topology.MaximalTorusData compactIdentityComponent where
  rank := 6
  hom := hom
  continuous := hom_continuous
  closedEmbedding := hom_closedEmbedding
  maximal := maximal_abelian

/-- No change of the induced map is hidden in the literature application. -/
theorem maximalTorusData_fundamentalMap :
    maximalTorusData.fundamentalMap = fundamentalMap := rfl

end Torus

/-- The sole external topology input. This abbreviation supplies no proof. -/
abbrev TorusSurjectivityLiteratureInput : Prop :=
  Math.Topology.MaximalTorusSurjectivityInput
    compactMatrixLieAlgebra compactIdentityComponent

theorem fundamentalMap_surjective_of_literature
    (hLiterature : TorusSurjectivityLiteratureInput) :
    Function.Surjective Torus.fundamentalMap :=
  hLiterature Torus.maximalTorusData

theorem fundamentalGroup_eq_one_of_literature
    (hLiterature : TorusSurjectivityLiteratureInput)
    (c : FundamentalGroup compactIdentityComponent 1) : c = 1 := by
  obtain ⟨a, rfl⟩ := fundamentalMap_surjective_of_literature hLiterature c
  exact Torus.fundamentalMap_apply_eq_one a

/-- Conditional on Proposition 38, not an unconditional/global instance. -/
theorem compactSimplyConnected_of_literature
    (hLiterature : TorusSurjectivityLiteratureInput) :
    SimplyConnectedSpace compactIdentityComponent := by
  let := compactPathConnected
  exact Math.Topology.simplyConnected_of_pi1_eq_one 1
    (fundamentalGroup_eq_one_of_literature hLiterature)

end

end Math.E6.Minuscule
