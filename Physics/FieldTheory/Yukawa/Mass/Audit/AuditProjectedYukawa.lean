import Physics.FieldTheory.Yukawa.Mass.ProjectedYukawa
import Physics.FieldTheory.Mass.Algebra.OrthogonalMass
import Physics.FieldTheory.Mass.Algebra.EquivariantWeylMassTransport
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Physics.ProjectedYukawa.diagonal, ``Physics.ProjectedYukawa.mixed,
    ``Physics.ProjectedYukawa.familyMass_form,
    ``Physics.ProjectedYukawa.generated_mass_eq_from_form,
    ``Physics.ProjectedYukawa.familyMass_congr,
    ``Physics.ProjectedYukawa.combine, ``Physics.OrthogonalMass.prod,
    ``Physics.OrthogonalMass.mem_radical, ``Physics.OrthogonalMass.radicalEquiv,
    ``Physics.OrthogonalMass.finrank_prod, ``Physics.OrthogonalMass.pair_radical,
    ``Physics.EquivariantWeylMassTransport.certificate_apply,
    ``Physics.EquivariantWeylMassTransport.PullbackCertificate.apply,
    ``Physics.EquivariantWeylMassTransport.PullbackCertificate.symm_apply,
    ``Physics.EquivariantWeylMassTransport.certificate_symm_apply]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Projected Yukawa: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Projected Yukawa: {declarations.length} strict axiom checks passed"
