import Physics.FieldTheory.Spinor.SixWeylInvariant
import Lean.Util.CollectAxioms

/-! Strict transitive axiom checks for six-right-Weyl invariant spanning. -/

run_cmd do
  let declarations := [
    ``GUT.SixWeylInvariant.basisValue_vanish,
    ``GUT.SixWeylInvariant.basis_ext,
    ``GUT.SixWeylInvariant.exists_pairing_coordinates]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Six-Weyl invariant spanning: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Six-Weyl invariant spanning: {declarations.length} strict transitive axiom checks passed"
