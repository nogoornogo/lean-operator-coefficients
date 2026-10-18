import Physics.StandardModel.Operators.LiSixQuarkLocalBasis
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! In addition to the strict axiom gate, check the actual proof dependency
chain: importing old data must not quietly retain the old inverse premise. -/
run_cmd do
  let env ← Lean.getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Symbolic inverse imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.LiSixQuarkCertificate.left_inverse,
    ``GUT.LiSixQuarkCertificate.right_inverse,
    ``GUT.LiSixQuarkCertificate.matrixEquiv,
    ``GUT.LiSixQuarkCertificate.coordinateEquiv,
    ``GUT.LiSixQuarkLocalBasis.localEquiv,
    ``GUT.LiSixQuarkLocalBasis.orbit_independent,
    ``GUT.LiSixQuarkLocalBasis.literal_reconstruction]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Symbolic inverse: {d} uses unexpected axiom {ax}"
  let forbidden := [`GUT.LiSixQuarkCertificate.inverseRational,
    `GUT.LiSixQuarkCertificate.rational_left_inverse,
    `GUT.LiSixQuarkCertificate.rational_right_inverse,
    `GUT.LiSixQuarkConvention.rationalCoordinates_eq,
    `GUT.LiSixQuarkCertificate.step_checked]
  let mut todo := ds.toArray
  let mut seen : Lean.NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if forbidden.contains n then
      throwError "Symbolic inverse depends on retired inverse premise {n}"
    -- Follow private helpers by their owning module as well. Math and
    -- dependency modules cannot refer back to Physics under the layer audit.
    let projectOwned := match env.getModuleIdxFor? n with
      | some idx =>
        let mod := env.header.moduleNames[idx.toNat]!
        (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod
      | none => (`GUT).isPrefixOf n
    if projectOwned then
      let some info := env.find? n | throwError "Missing inverse dependency {n}"
      for e in info.type :: (info.value? (allowOpaque := true)).toList do
        for dep in e.getUsedConstants do
          todo := todo.push dep
  Lean.logInfo m!"Li symbolic inverse: {ds.length} strict checks; old inverse premises absent"
