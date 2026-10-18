#!/usr/bin/env python3
"""Print one of six frozen Q18 cause-isolation probes; never executes Lean."""
import argparse
from pathlib import Path

STAGES = {
    'occupation6': 'theorem candidate : (∃ _ : GenerationTensorSupport.Occupation 6, True) := by decide +kernel',
    'occupation18': 'theorem candidate : (∃ _ : GenerationTensorSupport.Occupation 18, True) := by decide +kernel',
    'words18': 'theorem candidate : (∃ _ : (Fin 18 → Fin 3), True) := by decide +kernel',
    'metadata': '#eval expressionSize occupiedQ18\ntheorem candidate : expressionSize occupiedQ18 = 8000 := by decide +kernel',
    'occupied': 'theorem candidate : JointSourceExpression.Supports occupiedQ18 := by decide +kernel',
    'spins': 'theorem candidate : JointSourceExpression.Supports (eraseColor occupiedQ18) := by decide +kernel',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage', choices=STAGES)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent / 'probes'
    base = (root / 'diagnosis.lean.txt').read_text()
    controls = (root / 'controls.lean.txt').read_text()
    audit = '-- Strict transitive audit' + controls.split('-- Strict transitive audit', 1)[1]
    print(base + STAGES[args.stage] + '\n\n' + audit, end='')


if __name__ == '__main__':
    main()
