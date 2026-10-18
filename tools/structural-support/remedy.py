#!/usr/bin/env python3
"""Print a compact-occupation or isolated degree-six color remedy probe."""
import argparse
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage', choices=['compact', 'color-positive', 'color-negative'])
    args = parser.parse_args()
    root = Path(__file__).resolve().parent / 'probes'
    controls = (root / 'controls.lean.txt').read_text()
    audit = '-- Strict transitive audit' + controls.split('-- Strict transitive audit', 1)[1]
    if args.stage == 'compact':
        source = (root / 'compact.lean.txt').read_text()
    else:
        source = (root / 'diagnosis.lean.txt').read_text()
        source += '\n#synth Fintype (Equiv.Perm (Fin 6))\n'
        if args.stage == 'color-positive':
            source += 'theorem candidate : RestrictedColorWordSupport.Supports (.tensor (.leaf (.symmetric 6)) (.leaf (.oppositeSymmetric 6))) := by decide +kernel\n'
        else:
            source += 'theorem candidate : ¬ RestrictedColorWordSupport.Supports (.leaf (.symmetric 6)) := by decide +kernel\n'
    print(source + '\n' + audit, end='')


if __name__ == '__main__':
    main()
