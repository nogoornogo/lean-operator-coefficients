#!/usr/bin/env python3
"""Exact proposal generator for 2604.25134v2 Sec. 9.4, not a proof oracle.

Uses the independently defined epsilon probes from li-six-quark-check.py.
All emitted data must be checked by Lean, including literal seed correspondence.
No third-party dependencies; writes only stdout.
"""
import importlib.util
import itertools
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True

spec = importlib.util.spec_from_file_location(
    "local", Path(__file__).with_name("li-six-quark-check.py"))
local = importlib.util.module_from_spec(spec)
spec.loader.exec_module(local)

COLORS = [((1, 3, 4), (0, 2, 5)), ((1, 2, 4), (0, 3, 5))]
SPIN = ((0, 1), (2, 3), (4, 5))
SWAPS = [(0, 2), (1, 3), (3, 4), (4, 5)]


def proposal():
    probe_matrix = [[local.value(c, cv) * local.value(s, sv)
                     for c in local.colors for s in local.spins]
                    for cv, sv in local.local_probes]
    probe_inverse = local.inverse(probe_matrix)

    def coordinates(color, perm):
        values = [local.value(color, tuple(cv[perm[i]] for i in range(6))) *
                  local.value(SPIN, tuple(sv[perm[i]] for i in range(6)))
                  for cv, sv in local.local_probes]
        return [sum(a * b for a, b in zip(row, values)) for row in probe_inverse]

    seeds = [coordinates(c, tuple(range(6))) for c in COLORS]
    rows, selected, parents = [], [], []

    def add(seed, word, perm, parent):
        row = coordinates(COLORS[seed], perm)
        if local.rank(rows + [row]) > len(rows):
            rows.append(row)
            selected.append((seed, word, perm))
            parents.append(parent)

    for seed in range(2):
        add(seed, [], tuple(range(6)), None)
    pos = 0
    while pos < len(rows):
        seed, word, perm = selected[pos]
        for g, (a, b) in enumerate(SWAPS):
            swap = list(range(6))
            swap[a], swap[b] = b, a
            add(seed, word + [g], tuple(swap[perm[i]] for i in range(6)), (pos, g))
        pos += 1
    assert len(rows) == 25
    basis = list(map(list, zip(*rows)))
    inverse = local.inverse(basis)
    for a, b in [(basis, inverse), (inverse, basis)]:
        assert all(sum(a[i][k] * b[k][j] for k in range(25)) == int(i == j)
                   for i, j in itertools.product(range(25), repeat=2))
    return dict(seeds=seeds, selected=[(s, w) for s, w, _ in selected],
                parents=parents, basis=basis, inverse=inverse)


if __name__ == "__main__":
    data = proposal()
    if "--certificate-json" in sys.argv:
        print(json.dumps(data, default=str))
    else:
        print("Heeck-Le: two raw seeds; selected orbit basis rank 25; "
              "both rational inverse products checked (exploratory, not Lean).")
