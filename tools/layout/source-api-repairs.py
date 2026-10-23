#!/usr/bin/env python3
"""Replay bounded dependency/scheduling repairs; no statement/limit changes."""
from pathlib import Path
import json

PROOF_MODULE = 'import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkConventionalCoordinates\n\nopen Math\nopen scoped TensorProduct\nnamespace Physics.DeltaBTwoContractionRelations\nset_option autoImplicit false\nnoncomputable section\nopen SMEpsilonTensor\n\nset_option maxHeartbeats 4000000 in\nset_option maxRecDepth 100000 in\ntheorem fierz_blockAlternation\n    (u : Fin 2 → Color × Spin) (d : Fin 4 → Color × Spin) :\n    blockAlternation valueO2 u d - blockAlternation valueO1 u d =\n      3 * blockAlternation valueO3 u d := by\n  let v : Fin 6 → SixQuarkInvariant.Quark :=\n    ![(u 0).1 ⊗ₜ[ℂ] (u 0).2, (d 0).1 ⊗ₜ[ℂ] (d 0).2,\n      (u 1).1 ⊗ₜ[ℂ] (u 1).2, (d 1).1 ⊗ₜ[ℂ] (d 1).2,\n      (d 2).1 ⊗ₜ[ℂ] (d 2).2, (d 3).1 ⊗ₜ[ℂ] (d 3).2]\n  have he := congrArg\n    (fun f : SixQuarkTwoCoordinates.Sector => SixQuarkInvariant.exteriorRestriction f.1 v)\n    SixQuarkConventionalCoordinates.fierz\n  simp only [SixQuarkInvariant.exteriorRestriction_apply] at he\n  change SixQuarkInvariant.exteriorRestriction SixQuarkConventionalBasis.O2.1 v -\n    SixQuarkInvariant.exteriorRestriction SixQuarkConventionalBasis.O1.1 v =\n    3 * SixQuarkInvariant.exteriorRestriction SixQuarkConventionalBasis.O3.1 v at he\n  simpa only [v, SixQuarkConventionalCoordinates.O2_block,\n    SixQuarkConventionalCoordinates.O1_block,\n    SixQuarkConventionalCoordinates.O3_block] using he\n\nend\nend Physics.DeltaBTwoContractionRelations\n'

def apply_repairs():
    records = json.loads(Path('docs/topics/source-api-compatibility/proof-repairs.json').read_text())
    for record in records:
        full = Path(record['canonical'])
        source = full.read_text()
        marker = 'set_option maxHeartbeats 4000000 in\n'
        prefix, tail = source.split(marker, 1)
        old_statement = 'theorem fierz_blockAlternation' + tail.split('theorem fierz_blockAlternation',1)[1].split(' := by',1)[0]
        assert old_statement == record['statement'], 'Fierz statement changed'
        assert record['statement'] in PROOF_MODULE, 'Replacement statement changed'
        basic = Path(record['definitions'])
        basic.parent.mkdir(parents=True, exist_ok=True)
        basic.write_text(prefix+'end\nend Physics.DeltaBTwoContractionRelations\n')
        full.write_text(PROOF_MODULE)
        basis = full.with_name('SixQuarkConventionalBasis.lean')
        text = basis.read_text().replace('import '+record['canonical'][:-5].replace('/','.')+'\n',
            'import '+record['definitions'][:-5].replace('/','.')+'\n')
        basis.write_text(text)
    scheduling = Path('docs/topics/source-api-compatibility/execution-repairs.json')
    if scheduling.exists():
        for record in json.loads(scheduling.read_text()):
            assert record['kind'] == 'synchronous-certificate-elaboration'
            assert record['insertion'] in [
                '-- Elaborate the generated certificates sequentially within this module.\nset_option Elab.async false\n\n',
                '-- Elaborate the finite certificates sequentially within this module.\nset_option Elab.async false\n\n']
            source = Path(record['canonical'])
            text = source.read_text()
            assert text.count(record['marker']) == 1
            source.write_text(text.replace(record['marker'], record['insertion'] + record['marker'], 1))
    namespaces = Path('docs/topics/source-api-compatibility/namespace-repairs.json')
    if namespaces.exists():
        for record in json.loads(namespaces.read_text()):
            assert record['kind'] == 'namespace-resolution'
            source = Path(record['canonical'])
            text = source.read_text()
            for change in record['changes']:
                assert text.count(change['before']) == change['count']
                text = text.replace(change['before'], change['after'], change['count'])
            source.write_text(text)

if __name__ == '__main__':
    apply_repairs()
