import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkResidual
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! Consumer checks keep the retained rational API attached to the symbolic
source derivation, and follow private helpers in the proof dependency graph. -/
run_cmd do
  let env ← Lean.getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Structural Heeck-Le consumer imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let links := [
    (``Physics.HeeckLeSixQuarkCertificate.rationalSeedCoordinates, ``Physics.HeeckLeSixQuarkRecipe.seed),
    (``Physics.HeeckLeSixQuarkCertificate.basisRational, ``Physics.HeeckLeSixQuarkMatrix.basis),
    (``Physics.HeeckLeSixQuarkCertificate.inverseRational, ``Physics.HeeckLeSixQuarkMatrix.inverse),
    (``Physics.HeeckLeSixQuarkCertificate.rational_left_inverse, ``Physics.HeeckLeSixQuarkMatrix.left_inverse),
    (``Physics.HeeckLeSixQuarkCertificate.rational_right_inverse, ``Physics.HeeckLeSixQuarkMatrix.right_inverse)]
  for (decl, expected) in links do
    let some info := env.find? decl | throwError "Missing derived presentation {decl}"
    let some body := info.value? (allowOpaque := true) | throwError "Missing presentation body {decl}"
    unless body.getUsedConstants.contains expected do
      throwError "{decl} is detached from structural source {expected}"
  let roots := [``Physics.HeeckLeSixQuarkCertificate.left_inverse,
    ``Physics.HeeckLeSixQuarkCertificate.right_inverse,
    ``Physics.HeeckLeSixQuarkCertificate.coordinateEquiv,
    ``Physics.HeeckLeSixQuarkLocalBasis.localEquiv,
    ``Physics.HeeckLeSixQuarkLocalBasis.orbit_independent,
    ``Physics.HeeckLeSixQuarkLocalBasis.literal_reconstruction,
    ``Physics.HeeckLeSixQuarkResidual.physicalEquiv,
    ``Physics.HeeckLeSixQuarkResidual.onFieldsEquiv]
  for root in roots do
    for ax in (← Lean.collectAxioms root) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Structural Heeck-Le consumer {root} uses unexpected axiom {ax}"
  let retired := [`Physics.HeeckLeSixQuarkCertificate.step_checked,
    `Physics.HeeckLeSixQuarkCertificate.step_fun]
  let mut todo := roots.toArray
  let mut seen : Lean.NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    if retired.contains name then throwError "Consumer retains stepping-cache premise {name}"
    let owned := match env.getModuleIdxFor? name with
      | some idx => (`Physics).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => (`Physics).isPrefixOf name
    if owned then
      let some info := env.find? name | throwError "Missing consumer dependency {name}"
      for e in info.type :: (info.value? (allowOpaque := true)).toList do
        for dep in e.getUsedConstants do todo := todo.push dep
  unless seen.contains ``Physics.HeeckLeSixQuarkExtraction.extraction_rawAssembly do
    throwError "Physical consumers lost the symbolic source reconstruction dependency"
  Lean.logInfo m!"Structural Heeck-Le consumers: {roots.length} strict checks; {links.length} source links; private dependency traversal passed"
