#!/usr/bin/env python3
"""Freeze subject moves and declaration ownership from a successful build.

The JSON plan is review data, never a Lean proof premise. Applying it requires
the exact recorded source contents. Historical paths remain facades; only
canonical implementations are organized into the new subject directories.
"""
import argparse
import hashlib
import json
from pathlib import Path

TOPIC = Path('docs/topics/source-api-compatibility')
PLAN = TOPIC / 'layout-plan.json'


def module(file):
    return str(Path(file).with_suffix('')).replace('/', '.')


def math_subject(name):
    if any(s in name for s in ('Lagrangian', 'Density', 'AllOrder', 'PolynomialPotential')):
        return 'Lagrangian'
    if any(s in name for s in ('Jet', 'Derivative')):
        return 'Jets'
    if any(s in name for s in ('Prohibition', 'Protection', 'Selection', 'ChargeSelection')):
        return 'Protection'
    if name.startswith(('SU2', 'SL2', 'Doublet', 'TwistedSU2', 'WeakDoublet', 'WeightString')):
        return 'SU2'
    if name.startswith(('SU3', 'SL3', 'Color', 'RestrictedColor', 'DefiningTrace', 'JointColor')):
        return 'Color/SU3' if name.startswith(('SU3', 'SL3')) else 'Color/Diagrams'
    if 'Spurion' in name:
        return 'Spurions'
    if any(s in name for s in ('Higgs', 'WeakSinglet')):
        return 'Higgs'
    if any(s in name for s in ('Coefficient', 'Completeness', 'Input', 'CarrierPresentation')):
        return 'Coefficients'
    if any(s in name for s in ('Exterior', 'Alternat', 'Cauchy', 'Occupation')):
        return 'Exterior'
    if any(s in name for s in ('Symmetric', 'Symmetr', 'Bosonic')):
        return 'Symmetric'
    if any(s in name for s in ('Pattern', 'Species', 'Content', 'Generation', 'Family', 'Flavor')):
        return 'Content'
    if any(s in name for s in ('Torus', 'Weight', 'Cyclic', 'Circle', 'CompactTests')):
        return 'Weights'
    if any(s in name for s in ('Relation', 'Coinvariant', 'LocalHom', 'Exchange', 'Statistics', 'Statistical')):
        return 'Relations'
    if any(s in name for s in ('Tensor', 'Contraction', 'Pairing', 'TwoComponent', 'Young', 'FourSlot', 'SixSlot')):
        return 'Tensors'
    if any(s in name for s in ('Invariant', 'Covarian', 'Functional', 'Intertwiner', 'Equivalence')):
        return 'Invariants'
    return 'Constructions'


def operator_subject(name):
    if name.startswith('DevMohapatra'):
        return 'BaryonTwo/DevMohapatra'
    if name.startswith('LiSixQuark'):
        return 'BaryonTwo/Li'
    if name.startswith('HeeckLeSixQuark'):
        return 'BaryonTwo/HeeckLe'
    if any(s in name for s in ('DeltaBTwo', 'SixQuark')):
        return 'BaryonTwo/Coefficients'
    if 'Dipole' in name:
        return 'Dipole'
    if 'Qque' in name:
        return 'BaryonOne/Qque'
    if 'Qqql' in name:
        return 'BaryonOne/Qqql'
    if 'Duql' in name or 'Duue' in name:
        return 'BaryonOne/OtherFamilies'
    if name.startswith(('Bnv', 'GradedBnv', 'DeltaLOne', 'LiFourFamily', 'LiBasis', 'FourWeak')):
        return 'BaryonOne/Inputs'
    if any(s in name for s in ('Weinberg', 'LLHH')):
        return 'Weinberg'
    if name.startswith('SMB1') or any(s in name for s in ('Minimum', 'Dimension', 'DegreeBounds')):
        return 'Support/Dimension'
    if name.startswith(('SMQ', 'SMColor', 'SMColored', 'SMQuark')):
        return 'Support/Quark'
    if name.startswith(('SMLepton', 'SML')):
        return 'Support/Lepton'
    if name.startswith(('SMJoint', 'SMSigned', 'SMCombined', 'SMMixed')):
        return 'Support/Joint'
    if name.startswith(('SMCompact', 'SMComputable', 'SMFinite', 'SMGeneration', 'SMLower')):
        return 'Support/Decomposition'
    if name.startswith('SM'):
        return 'Support/Coordinates'
    if 'Higgs' in name:
        return 'Higgs'
    return 'Selection'


def jet_subject(name):
    if name.startswith('HiggsQuarticFour'):
        return 'Higgs/QuarticFour'
    if name.startswith('Higgs'):
        return 'Higgs/Inputs'
    if name.startswith('ScalarQuarticFour'):
        return 'Scalar/QuarticFour'
    if name.startswith('WeylHiggs'):
        return 'Weyl/Higgs'
    if any(s in name for s in ('Lagrangian', 'Yukawa', 'EulerDensity')):
        return 'Lagrangian'
    if name.startswith(('Maxwell', 'YangMills', 'FormalYangMills', 'AbelianFieldStrength')):
        return 'Gauge'
    if 'Weyl' in name:
        return 'Weyl/Equations'
    if name.startswith('Lorentz'):
        return 'Lorentz'
    return 'Scalar/Inputs'


def target(file):
    p = Path(file)
    name = p.stem.removeprefix('Audit')
    is_audit = p.parent.name == 'Audit'
    parent = p.parent.parent if is_audit else p.parent
    subject = None
    if str(parent) == 'Math/RepresentationTheory':
        subject = math_subject(name)
    elif str(parent) == 'Math/LinearAlgebra':
        subject = ('Quaternion' if 'Quaternion' in name else
                   'Exterior' if 'Exterior' in name or 'Alternat' in name else
                   'Symmetric' if 'Symmetric' in name else
                   'Selection' if any(s in name for s in ('Select', 'Coefficient', 'Completeness', 'Mediator')) else
                   'Tensor' if 'Tensor' in name else
                   'Matrix' if any(s in name for s in ('Matrix', 'Hermitian', 'Takagi', 'Unitary')) else
                   'Constructions')
    elif str(parent) == 'Math/Algebra':
        subject = ('Variational' if any(s in name for s in ('Euler', 'Variation', 'Lagrangian')) else
                   'Jets' if any(s in name for s in ('Jet', 'IBP', 'EOM', 'Differential', 'PolynomialPotential', 'Density')) else
                   'Waves' if any(s in name for s in ('Wave', 'Cubature', 'HiggsFour', 'Mandelstam', 'Lorentz')) else
                   'Constructions')
    elif str(parent) == 'Physics/StandardModel/Operators':
        subject = operator_subject(name)
    elif str(parent) == 'Physics/FieldTheory/Jets':
        subject = jet_subject(name)
    elif str(parent) == 'Physics/FieldTheory/Mass':
        subject = ('Spectrum' if any(s in name for s in ('Spectrum', 'Index', 'ChiralAction', 'VirtualRealization')) else
                   'Flavor' if 'Flavor' in name else
                   'Surplus' if any(s in name for s in ('Copy', 'Surplus', 'Surjective', 'Species', 'Spectator')) else
                   'Algebra')
    elif str(parent) == 'Physics/StandardModel/Spectrum':
        subject = ('Mass' if any(s in name for s in ('Mass', 'Radical', 'Light', 'ZeroMode')) else
                   'Charges' if any(s in name for s in ('Charge', 'Profile', 'Triality', 'Baryon')) else
                   'Representations')
    elif str(parent) == 'Physics/StandardModel/Gauge':
        subject = ('Charges' if any(s in name for s in ('Charge', 'Torus', 'Hypercharge', 'Abelian')) else 'Tensors')
    elif str(parent) == 'Physics/FieldTheory/Spinor':
        subject = 'Tensors' if any(s in name for s in ('Tensor', 'Contraction', 'Fierz', 'Pair', 'Invariant')) else 'Weyl'
    elif str(parent) == 'Physics/FieldTheory/Yukawa':
        subject = 'Actions' if any(s in name for s in ('Action', 'Symmetry', 'Stabilizer')) else 'Mass'
    if subject:
        return str(parent / subject / ('Audit' if is_audit else '') / p.name)
    # Smaller remaining Physics families still need a separate legacy facade
    # when their declarations change root namespace.
    if file.startswith('Physics/'):
        return str(parent / 'Core' / ('Audit' if is_audit else '') / p.name)
    return file


def freeze(metadata_file, constants_file):
    if PLAN.exists():
        raise SystemExit('A frozen plan already exists; do not use partial-build metadata.')
    metadata = json.loads(Path(metadata_file).read_text())
    constants = json.loads(Path(constants_file).read_text())
    pilot = 'Physics/FieldTheory/Mass/AbelianMassSpectrum.lean'
    pilot_input = 'Physics/FieldTheory/Mass/Spectrum/AbelianMassSpectrum.lean'
    paths = []
    for old in sorted(metadata):
        source = pilot_input if old == pilot else old
        paths.append(dict(old=old, new=target(old), input=source,
                          sha256=hashlib.sha256(Path(source).read_bytes()).hexdigest(),
                          dependencies=[d[0] for d in metadata[old]['directImports']]))
    destinations = [p['new'] for p in paths]
    assert len(destinations) == len(set(destinations)), 'Destination collision'
    entries = []
    for c in sorted(constants, key=lambda c: c['name']):
        n = c['name']
        if c['module'].startswith('Physics.') and n.startswith('GUT.'):
            # Compiler auxiliaries/private names are explicitly not public API.
            if '._' not in n and '.match_' not in n:
                entries.append(dict(old=n, new='Physics.' + n[4:],
                                    module=c['module'], kind=c['kind']))
    plan = dict(kind='frozen-source-api-plan', migration='source-api-v1',
                input='successful branch build, elaborated constant ownership and source hashes',
                publicationBaseline='local publish/v1.0; external deployment not verified',
                paths=paths, entries=entries,
                physicsUsers=[f for f, d in metadata.items() if any(
                    json.loads(key).get('c', {}).get('m', '').startswith('Physics.')
                    for key in d['references'])],
                physicsOwned=[c['name'] for c in constants if c['module'].startswith('Physics.')],
                applicationOwned=[c['name'] for c in constants if c['module'].startswith('GUT.')])
    PLAN.write_text(json.dumps(plan, indent=2) + '\n')
    print(f'Frozen {len(paths)} source paths, {len(entries)} protected Physics names')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--metadata', required=True)
    parser.add_argument('--constants', required=True)
    args = parser.parse_args()
    freeze(args.metadata, args.constants)
