import Math.LieGroups.E6.Minuscule.FundamentalGroupSurjectivity
import Math.LieGroups.E6.Minuscule.CompactSmoothTorus
import Math.LieGroups.E6.Minuscule.SingularLocus
import Math.Topology.CentralizerTopology
import Math.Topology.RootSpace
import Math.Topology.CoveringBundle
import Lean.Util.CollectAxioms

/-! The audit checks conditional implications and actual geometric inputs.
Standard axioms do NOT mean the literature input has been proved. -/

set_option autoImplicit false

namespace Math.E6.Audit.LiteratureTopology

open Minuscule
open scoped Manifold Matrix.Norms.L2Operator ContDiff

example : CompactSpace compactIdentityComponent := inferInstance
example : ConnectedSpace compactIdentityComponent := inferInstance
example : T2Space compactIdentityComponent := inferInstance
example : FiniteDimensional ℝ compactMatrixLieAlgebra := inferInstance
example : LieGroup 𝓘(ℝ, compactMatrixLieAlgebra) ∞ compactIdentityComponent := inferInstance
example : IsManifold 𝓘(ℝ, compactMatrixLieAlgebra) ∞ compactIdentityComponent := inferInstance

example : Torus.maximalTorusData.hom = Torus.hom := rfl
example : Torus.maximalTorusData.fundamentalMap = Torus.fundamentalMap := rfl
example : Topology.IsClosedEmbedding Torus.maximalTorusData.hom :=
  Torus.maximalTorusData.closedEmbedding

example (hLiterature : TorusSurjectivityLiteratureInput) :
    SimplyConnectedSpace compactIdentityComponent :=
  compactSimplyConnected_of_literature hLiterature

-- Guard against silently publishing the conditional result as a global instance.
example : True := by
  fail_if_success
    have : SimplyConnectedSpace compactIdentityComponent := inferInstance
  trivial

-- The identity is not a regular torus point. Do not reintroduce T <= G_reg.
example : ¬ Torus.isRegular 1 := by
  intro h
  exact h 0 (Torus.rootChar_one 0)

end Math.E6.Audit.LiteratureTopology

run_cmd do
  let declarations := [
    ``Math.Topology.MaximalTorusData.fundamentalMap,
    ``Math.Topology.MaximalTorusSurjectivityInput,
    ``Math.Topology.simplyConnected_of_pi1_eq_one,
    ``Math.E6.Minuscule.Torus.maximalTorusData,
    ``Math.E6.Minuscule.Torus.maximalTorusData_fundamentalMap,
    ``Math.E6.Minuscule.TorusSurjectivityLiteratureInput,
    ``Math.E6.Minuscule.fundamentalMap_surjective_of_literature,
    ``Math.E6.Minuscule.fundamentalGroup_eq_one_of_literature,
    ``Math.E6.Minuscule.compactSimplyConnected_of_literature,
    ``Math.E6.Minuscule.compactPathConnected,
    ``Math.E6.Minuscule.Torus.hom_contMDiff,
    ``Math.E6.Minuscule.Torus.genericPoint_regular,
    ``Math.E6.Minuscule.Torus.isClosed_singularLocus,
    ``Math.E6.Minuscule.Torus.singularLocus_union_kernels_subset]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6 literature topology: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6 literature topology: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6 literature topology: checked {declarations.length} declarations; literature input remains explicit"
