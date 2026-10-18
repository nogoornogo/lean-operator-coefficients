#!/usr/bin/env python3
"""Materialize a bounded Lean feasibility probe; does not execute or accept it."""
import argparse
from pathlib import Path

TEMPLATES = Path(__file__).resolve().parent / 'probes'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage', choices=['direct', 'controls', 'q6', 'q18',
                                          'neutral-zero', 'reject-positive',
                                          'reject-negative', 'compiled'])
    args = parser.parse_args()
    base = 'direct' if args.stage == 'direct' else 'controls'
    source = (TEMPLATES / (base + '.lean.txt')).read_text()
    additions = {
        'q6': 'theorem candidate : SMJointHiggsSupport.HiggsSupport (fun _ : Fin 6 => 0) 0 2 := by decide +kernel',
        'q18': 'theorem candidate : SMJointHiggsSupport.HiggsSupport (fun _ : Fin 18 => 0) 0 6 := by decide +kernel',
        'neutral-zero': 'theorem candidate : ¬ SMJointContentSupport.Supports (fun s => if s = 0 then 24 else 0) 14 := by decide +kernel',
        'reject-positive': 'theorem candidate : SU2TensorWordSupport.Supports (.leaf 1) := by decide +kernel',
        'reject-negative': 'theorem candidate : ¬ SU2TensorWordSupport.Supports (.leaf 0) := by decide +kernel',
        'compiled': '#eval decide (SMJointHiggsSupport.HiggsSupport (fun _ : Fin 2 => 3) 2 0)',
    }
    # Place added declarations before the audit so it also covers each candidate.
    if args.stage in additions:
        marker = '-- Strict transitive audit'
        before, after = source.split(marker, 1)
        source = before + additions[args.stage] + '\n\n' + marker + after
    print(source, end='')


if __name__ == '__main__':
    main()
