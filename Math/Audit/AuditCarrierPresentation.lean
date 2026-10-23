import Math.Audit.ImportOrigin
import Math.RepresentationTheory.Coefficients.CarrierPresentation

/-! Strict actual-source return audit for distinct algebraic carriers. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Carrier presentation imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.CarrierPresentation.actionAlong,
    ``Math.CarrierPresentation.equivAlong,
    ``Math.CarrierPresentation.actionAlong_det,
    ``Math.CarrierPresentation.Carrier.linearEquiv,
    ``Math.CarrierPresentation.Carrier.action,
    ``Math.CarrierPresentation.Carrier.representationEquiv,
    ``Math.CarrierPresentation.selfDuality,
    ``Math.CarrierPresentation.injection,
    ``Math.CarrierPresentation.injection_injective,
    ``Math.CarrierPresentation.coefficientEquiv,
    ``Math.CarrierPresentation.allowed]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Carrier presentation {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Distinct carrier presentation: {ds.length} strict transitive checks passed"
