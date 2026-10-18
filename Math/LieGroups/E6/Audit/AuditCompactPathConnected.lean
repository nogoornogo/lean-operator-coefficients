import Math.LieGroups.E6.Minuscule.CompactPathConnected
import Lean.Util.CollectAxioms

/-! Path connectedness of the compact identity component and its torus coset space,
with axiom audit. -/

set_option autoImplicit false

namespace Math.E6.Audit.CompactPathConnected

noncomputable section

open Math.E6.Minuscule

/-- The compact identity component is path-connected. -/
example : PathConnectedSpace compactIdentityComponent :=
  compactPathConnected

/-- The coset space by the torus subgroup is path-connected. -/
example : PathConnectedSpace
    (compactIdentityComponent ⧸ Torus.subgroup) :=
  torusCosetPathConnected

end

end Math.E6.Audit.CompactPathConnected

run_cmd do
  let declarations := [
    ``Math.E6.Minuscule.compactPathConnected,
    ``Math.E6.Minuscule.torusCosetPathConnected]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6 path connectedness audit: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6 path connectedness audit: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6 path connectedness audit: checked {declarations.length} declarations"
