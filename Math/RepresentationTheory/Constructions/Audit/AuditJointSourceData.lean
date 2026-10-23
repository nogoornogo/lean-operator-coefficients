import Math.RepresentationTheory.Color.Diagrams.ColoredSourceData
import Math.RepresentationTheory.Content.JointContentData
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "joint source Math audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.JointSourceData.scalar,
    ``Math.JointSourceData.color,
    ``Math.JointSourceData.weak,
    ``Math.JointSourceData.spin,
    ``Math.JointSourceData.pair,
    ``Math.JointSourceData.single,
    ``Math.JointSourceData.doubletPair,
    ``Math.JointSourceData.single_eq,
    ``Math.JointSourceData.doubletPair_eq,
    ``Math.JointSourceData.branchCount,
    ``Math.JointSourceData.dualKind,
    ``Math.JointSourceData.dual,
    ``Math.JointSourceData.dual_eq,
    ``Math.JointSourceData.sums,
    ``Math.JointSourceData.colorWeak,
    ``Math.JointSourceData.coloredOne,
    ``Math.JointSourceData.coloredTwo,
    ``Math.JointSourceData.coloredThree,
    ``Math.JointSourceData.colored,
    ``Math.JointSourceData.colored_eq,
    ``Math.JointSourceData.conjugateColored_eq,
    ``Math.JointSourceData.qOne,
    ``Math.JointSourceData.qTwo,
    ``Math.JointSourceData.qThree,
    ``Math.JointSourceData.qFourth,
    ``Math.JointSourceData.qK211,
    ``Math.JointSourceData.qK22,
    ``Math.JointSourceData.qFour,
    ``Math.JointSourceData.qFifthOne,
    ``Math.JointSourceData.qFifthThree,
    ``Math.JointSourceData.qFive,
    ``Math.JointSourceData.qSixthZero,
    ``Math.JointSourceData.qSixthTwo,
    ``Math.JointSourceData.qSixthFour,
    ``Math.JointSourceData.qSix,
    ``Math.JointSourceData.quark,
    ``Math.JointSourceData.qOne_eq,
    ``Math.JointSourceData.qTwo_eq,
    ``Math.JointSourceData.qThree_eq,
    ``Math.JointSourceData.qFour_eq,
    ``Math.JointSourceData.qFive_eq,
    ``Math.JointSourceData.qSix_eq,
    ``Math.JointSourceData.qComplement7_eq,
    ``Math.JointSourceData.qComplement8_eq,
    ``Math.JointSourceData.qComplement9_eq,
    ``Math.JointSourceData.qComplement10_eq,
    ``Math.JointSourceData.qComplement11_eq,
    ``Math.JointSourceData.qTop_eq,
    ``Math.JointSourceData.quark_eq,
    ``Math.JointSourceData.conjugateQuark_eq,
    ``Math.JointContentData.Index,
    ``Math.JointContentData.generations,
    ``Math.JointContentData.occupied,
    ``Math.JointContentData.choiceEquiv,
    ``Math.JointContentData.generations_eq,
    ``Math.JointContentData.occupied_eq]
  for d in ds do
    let env ← Lean.getEnv
    unless (env.getModuleIdxFor? d).isSome do
      throwError "missing original module for {d}"
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "joint source data audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"joint source data: {ds.length} strict transitive checks passed"
