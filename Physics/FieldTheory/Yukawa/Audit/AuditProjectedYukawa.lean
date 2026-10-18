import Physics.FieldTheory.Yukawa.ProjectedYukawa
import Physics.FieldTheory.Mass.OrthogonalMass
import Physics.FieldTheory.Mass.EquivariantWeylMassTransport
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.ProjectedYukawa.diagonal, ``GUT.ProjectedYukawa.mixed,
    ``GUT.ProjectedYukawa.familyMass_form,
    ``GUT.ProjectedYukawa.generated_mass_eq_from_form,
    ``GUT.ProjectedYukawa.familyMass_congr,
    ``GUT.ProjectedYukawa.combine, ``GUT.OrthogonalMass.prod,
    ``GUT.OrthogonalMass.mem_radical, ``GUT.OrthogonalMass.radicalEquiv,
    ``GUT.OrthogonalMass.finrank_prod, ``GUT.OrthogonalMass.pair_radical,
    ``GUT.EquivariantWeylMassTransport.certificate_apply,
    ``GUT.EquivariantWeylMassTransport.PullbackCertificate.apply,
    ``GUT.EquivariantWeylMassTransport.PullbackCertificate.symm_apply,
    ``GUT.EquivariantWeylMassTransport.certificate_symm_apply]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Projected Yukawa: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Projected Yukawa: {declarations.length} strict axiom checks passed"
