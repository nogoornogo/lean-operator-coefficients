import GUT.PatiSalam.Embeddings.PhiRepresentation
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod && !(`GUT.PatiSalam).isPrefixOf mod then
      throwError "PS representation admission imports another model {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``GUT.PatiSalam.StandardModelEmbedding.rawMatrix_unitary,
    ``GUT.PatiSalam.StandardModelEmbedding.rawMatrix_det,
    ``GUT.PatiSalam.StandardModelEmbedding.matrixHom_unitary,
    ``GUT.PatiSalam.StandardModelEmbedding.matrixHom_det,
    ``GUT.PatiSalam.StandardModelEmbedding.rightMatrix_unitary,
    ``GUT.PatiSalam.StandardModelEmbedding.rightMatrix_det,
    ``GUT.PatiSalam.StandardModelEmbedding.hom,
    ``GUT.PatiSalam.ComponentRepresentations.colorIn_equivariant,
    ``GUT.PatiSalam.ComponentRepresentations.leptonIn_equivariant,
    ``GUT.PatiSalam.ComponentRepresentations.qIn_equivariant,
    ``GUT.PatiSalam.ComponentRepresentations.lIn_equivariant,
    ``GUT.PatiSalam.ComponentRepresentations.uIn_equivariant,
    ``GUT.PatiSalam.ComponentRepresentations.dIn_equivariant,
    ``GUT.PatiSalam.ComponentRepresentations.nIn_equivariant,
    ``GUT.PatiSalam.ComponentRepresentations.eIn_equivariant,
    ``GUT.PatiSalam.ComponentRepresentations.leftEquiv,
    ``GUT.PatiSalam.ComponentRepresentations.rightEquiv,
    ``GUT.PatiSalam.ComponentRepresentations.leftSplit_equivariant,
    ``GUT.PatiSalam.ComponentRepresentations.rightSplit_equivariant,
    ``GUT.PatiSalam.ComponentRepresentations.leftAdmission,
    ``GUT.PatiSalam.ComponentRepresentations.rightAdmission,
    ``GUT.PatiSalam.ComponentRepresentations.leftProjection,
    ``GUT.PatiSalam.ComponentRepresentations.rightProjection,
    ``GUT.PatiSalam.ComponentRepresentations.leftProjection_admission,
    ``GUT.PatiSalam.ComponentRepresentations.rightProjection_admission,
    ``GUT.PatiSalam.ComponentRepresentations.leftAdmission_projection,
    ``GUT.PatiSalam.ComponentRepresentations.rightAdmission_projection,
    ``GUT.PatiSalam.ComponentRepresentations.leftAdmission_injective,
    ``GUT.PatiSalam.ComponentRepresentations.rightAdmission_injective,
    ``GUT.PatiSalam.ComponentRepresentations.arrayRepresentation,
    ``GUT.PatiSalam.ComponentRepresentations.array_intertwines,
    ``GUT.PatiSalam.ComponentRepresentations.chiRepresentation_neutral,
    ``GUT.PatiSalam.ComponentRepresentations.array_dIn_single,
    ``GUT.PatiSalam.ComponentRepresentations.array_nIn,
    ``GUT.PatiSalam.PhiRepresentation.equiv,
    ``GUT.PatiSalam.PhiRepresentation.admission,
    ``GUT.PatiSalam.PhiRepresentation.split_equivariant,
    ``GUT.PatiSalam.PhiRepresentation.diagonal_vacuum,
    ``GUT.PatiSalam.PhiRepresentation.join_equivariant,
    ``GUT.PatiSalam.PhiRepresentation.inclusion]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "PS representation admission {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"PS representation admission: model boundary and {ds.length} strict transitive checks passed"
