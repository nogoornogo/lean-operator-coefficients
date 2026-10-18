import GUT.SUN.Matching.ConjugatedControls
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.SUN.ConjugatedMatter.conjugate_matrix,
    ``GUT.SUN.ConjugatedMatter.inclusion_injective,
    ``GUT.SUN.ConjugatedMatter.project_embed,
    ``GUT.SUN.ConjugatedMatter.exterior_rotation,
    ``GUT.SUN.ConjugatedMatter.matter_embed,
    ``GUT.SUN.ConjugatedMatter.coreAction_eq,
    ``GUT.SUN.ConjugatedMatter.background_trace,
    ``GUT.SUN.ConjugatedMatter.background_hermitian,
    ``GUT.SUN.ConjugatedMatter.mass_conjugate,
    ``GUT.SUN.ConjugatedMatter.mass_zero_iff,
    ``GUT.SUN.ConjugatedMatter.upper_mass,
    ``GUT.SUN.ConjugatedMatter.lower_mass,
    ``GUT.SUN.ConjugatedMatter.upCurrent_eq,
    ``GUT.SUN.ConjugatedMatter.electronCurrent_eq,
    ``GUT.SUN.ConjugatedMatching.rawLeft_eq,
    ``GUT.SUN.ConjugatedMatching.rawRight_eq,
    ``GUT.SUN.ConjugatedMatching.rawInvariant,
    ``GUT.SUN.ConjugatedMatching.coefficient_eq,
    ``GUT.SUN.ConjugatedMatching.generated_eq,
    ``GUT.SUN.ConjugatedMatching.generated_nonzero,
    ``GUT.SUN.ConjugatedMatching.action_eq,
    ``GUT.SUN.ConjugatedMatching.full_action_eq,
    ``GUT.SUN.ConjugatedControls.rotation_one,
    ``GUT.SUN.ConjugatedControls.rotation_mul,
    ``GUT.SUN.ConjugatedControls.background_one,
    ``GUT.SUN.ConjugatedControls.background_mul,
    ``GUT.SUN.ConjugatedControls.inclusion_one,
    ``GUT.SUN.ConjugatedControls.inclusion_mul,
    ``GUT.SUN.ConjugatedControls.identity_generated,
    ``GUT.SUN.ConjugatedControls.su7_generated]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Conjugated matching: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Conjugated matching: {declarations.length} strict axiom checks passed"
