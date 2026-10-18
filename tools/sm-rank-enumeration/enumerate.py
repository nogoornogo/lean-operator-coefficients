"""Exact bounded q/l recount and finite-table size diagnostic (no Lean oracle).

Run without arguments for JSON; --csv emits every candidate to stdout.
Only the previously certified bounded predicates are evaluated here.
"""
import argparse
import csv
import json
import math
import sys
from collections import Counter
from pathlib import Path


def orbit(k, q, l):
    return sorted({(u*q % k, u*l % k) for u in range(k) if math.gcd(u, k) == 1})


def enumerate_candidates():
    rows = []
    for k in range(2, 13):
        for q in range(k):
            for l in range(k):
                if (3*q+l) % k == 0:
                    continue
                representative = min(orbit(k, q, l))
                rows.append(dict(k=k, q=q, l=l,
                    orbit_q=representative[0], orbit_l=representative[1],
                    effective_order=k//math.gcd(k, q, l),
                    bounded_b2_forbidden=bool(6*q % k),
                    bounded_llhh_forbidden=bool(2*l % k)))
    return rows


def report(rows):
    counts = Counter(r['k'] for r in rows)
    orbit_counts = {k: len({(r['orbit_q'], r['orbit_l']) for r in rows if r['k'] == k})
                    for k in range(2, 13)}
    profiles = Counter((r['bounded_b2_forbidden'], r['bounded_llhh_forbidden']) for r in rows)
    effective = Counter(r['effective_order'] for r in rows)
    # Compare separate arithmetic enumeration to committed Lean count theorems.
    assert sum(k*k for k in range(2, 13)) == 649
    assert len(rows) == 572
    assert [counts[k] for k in range(2, 13)] == [k*(k-1) for k in range(2, 13)]
    assert list(orbit_counts.values()) == [2, 3, 7, 5, 16, 7, 18, 14, 24, 11, 44]
    assert sum(orbit_counts.values()) == 151
    assert [profiles[b, l] for b in (False, True) for l in (False, True)] == [20, 166, 70, 316]
    assert [effective[k] for k in range(2, 13)] == [12, 24, 30, 40, 44, 42, 44, 66, 68, 110, 92]
    for r in rows:
        points = orbit(r['k'], r['q'], r['l'])
        assert (r['q'], r['l']) in points
        assert all((3*q+l) % r['k'] for q, l in points)
        assert all(orbit(r['k'], q, l) == points for q, l in points)
        assert len({(r['q']*g % r['k'], r['l']*g % r['k'])
                    for g in range(r['k'])}) == r['effective_order']
    dimensions = [36, 18, 18, 12, 6, 36, 18, 18, 12, 6]
    assert sum(dimensions) == 180
    patterns = sum(10**n for n in range(181))
    # Hypothetical multiplicity compression, before gauge/charge filtering.
    content_box = math.prod(d+1 for d in dimensions)
    return dict(scope='bounded predicates only; all-degree support not evaluated',
        initial_assignments=649, candidates=len(rows), unit_orbits=sum(orbit_counts.values()),
        by_order=[dict(k=k, candidates=counts[k], orbits=orbit_counts[k]) for k in range(2, 13)],
        bounded_profiles=[dict(b2_forbidden=b, llhh_forbidden=l, count=profiles[b, l])
                          for b in (False, True) for l in (False, True)],
        effective_orders=dict(sorted(effective.items())),
        table_size=dict(species_dimensions=dimensions, ordered_patterns=str(patterns),
            literal_table_entries=str(patterns*181**2),
            capacity_bounded_content_box=content_box,
            middle_degree_exterior_dimension=str(math.comb(180, 90))),
        rank_status='no executable basis or exact coefficient backend for SMFullLocalKernel')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--csv', action='store_true')
    args = parser.parse_args()
    rows = enumerate_candidates()
    summary = report(rows)
    committed = Path(__file__).with_name('candidates.csv')
    if committed.exists():
        with committed.open(newline='') as stream:
            saved = list(csv.DictReader(stream))
        assert saved == [{key: str(value) for key, value in row.items()} for row in rows]
    if args.csv:
        writer = csv.DictWriter(sys.stdout, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    else:
        print(json.dumps(summary, indent=2))
