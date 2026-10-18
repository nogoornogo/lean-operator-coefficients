import Math.LieGroups.E6.Minuscule.CompactAtlas
import Math.LieGroups.E6.Minuscule.CompactTorus
import Lean.Util.CollectAxioms

/-!
# Path connectedness of the compact identity component and its torus coset space

The identity component is path-connected because it is a connected Lie group
modeled on a finite-dimensional real vector space.  The coset space by the
torus subgroup inherits path-connectedness via the continuous quotient projection.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Manifold

/-- The compact identity component is path-connected. -/
theorem compactPathConnected : PathConnectedSpace compactIdentityComponent := by
  have h_loc : LocallyPathConnectedSpace compactMatrixLieAlgebra := inferInstance
  have h_loc' : LocallyPathConnectedSpace compactIdentityComponent :=
    ChartedSpace.locallyPathConnectedSpace (M := compactIdentityComponent)
      (H := compactMatrixLieAlgebra)
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-- The coset space of the compact identity component by the torus subgroup
is path-connected. -/
theorem torusCosetPathConnected :
    PathConnectedSpace
      (compactIdentityComponent ⧸ Torus.subgroup) := by
  have h_loc : LocallyPathConnectedSpace compactMatrixLieAlgebra := inferInstance
  have h_loc' : LocallyPathConnectedSpace compactIdentityComponent :=
    ChartedSpace.locallyPathConnectedSpace (M := compactIdentityComponent)
      (H := compactMatrixLieAlgebra)
  have h_pc : PathConnectedSpace compactIdentityComponent :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  have h_surj : Function.Surjective (QuotientGroup.mk :
    compactIdentityComponent → compactIdentityComponent ⧸ Torus.subgroup) := by
    rintro ⟨q⟩
    exact ⟨q, rfl⟩
  have h_cont : Continuous (QuotientGroup.mk :
    compactIdentityComponent → compactIdentityComponent ⧸ Torus.subgroup) :=
    QuotientGroup.continuous_mk
  exact h_surj.pathConnectedSpace h_cont

end

end Math.E6.Minuscule

run_cmd do
  let declarations := [
    ``Math.E6.Minuscule.compactPathConnected,
    ``Math.E6.Minuscule.torusCosetPathConnected]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6 path connectedness: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6 path connectedness: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6 path connectedness: checked {declarations.length} declarations"
