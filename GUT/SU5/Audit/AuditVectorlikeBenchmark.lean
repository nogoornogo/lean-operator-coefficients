import GUT.SU5.SelectionRules.VectorlikeBenchmark
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.SU5.VectorlikeBenchmark.decomposition,
    ``GUT.SU5.VectorlikeBenchmark.joint_continuous,
    ``GUT.SU5.VectorlikeBenchmark.compatible_continuous,
    ``GUT.SU5.VectorlikeBenchmark.extension,
    ``GUT.SU5.VectorlikeBenchmark.quark_extra_positive,
    ``GUT.SU5.VectorlikeBenchmark.not_exact,
    ``GUT.SU5.VectorlikeBenchmark.shared_positive,
    ``GUT.SU5.VectorlikeBenchmark.exists_actual_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Vectorlike SU5 benchmark: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Vectorlike SU5 benchmark: {declarations.length} strict axiom checks passed"
