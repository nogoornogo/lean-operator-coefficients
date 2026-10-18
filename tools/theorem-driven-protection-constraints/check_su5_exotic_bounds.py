"""Complete formal characters and symbolic copy-index constraints, not Lean branching."""
import ast
from collections import Counter
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import runpy

root = Path(__file__).resolve().parents[2]
lib = runpy.run_path(str(root / 'tools/su6-light-placement-search/check_small_branching.py'))
f = lib['F'][:5]
sums, tensor, negate, difference, decompose = (lib[k] for k in
    ('sums', 'tensor', 'negate', 'difference', 'decompose'))
ext = lambda k: sums(f, combinations(range(5), k))
ten = ext(2)
forty = negate(difference(tensor(Counter(f), ten), ext(3)))
ten_weights = [w for w, m in ten.items() for _ in range(m)]
fifty = difference(sums(ten_weights, combinations_with_replacement(range(10), 2)), ext(4))
chars = {'10': ten, 'bar5': negate(Counter(f)), '40': forty, '50': fifty}
branches = {}
conj = lambda w: (w[1], w[0], w[2], -w[3])
for name, char in chars.items():
    branch = decompose(char)
    rebuilt = Counter()
    for label, m in branch.items():
        rebuilt.update({w: n*m for w, n in lib['irrep'](*label).items()})
    assert rebuilt == char
    assert sum(char.values()) == int(name.removeprefix('bar'))
    branches[name] = branch

Q, U, E = (1,0,1,1), (0,1,0,-4), (0,0,0,6)
expected = {'10': (1,1,1), 'bar5': (0,0,0), '40': (1,1,0), '50': (0,0,0)}
for name, branch in branches.items():
    assert tuple(branch.get(w,0) for w in (Q,U,E)) == expected[name]
    assert all(branch.get(conj(w),0) == 0 for w in (Q,U,E))

# Sparse chiral-index rows for signed net copy counts (10,bar5,40,50).
# Non-SM witnesses: color octet at 6Y=6 and singlet at 6Y=12.
octet, charged = (1,1,0,6), (0,0,0,12)
index = lambda branch,w: branch.get(w,0)-branch.get(conj(w),0)
assert tuple(index(branches[n], octet) for n in chars) == (0,0,1,0)
assert tuple(index(branches[n], charged) for n in chars) == (0,0,0,1)
assert tuple(index(branches[n], E) for n in chars) == (1,0,0,0)
L = (0,0,1,-3)
assert tuple(index(branches[n], L) for n in chars) == (0,1,0,0)

# Thus exact SM-only index of N generations forces net40=net50=0,
# net10=netbar5=N. The proof is these row identities, not bounded sampling.
print('All complete characters reconstruct, dimensions 10/5/40/50 checked.')
for name, branch in branches.items():
    print(name, sorted(branch.items()))
print('SM-only index forces net40=net50=0 and net10=netbar5=N.')
print('Q,U surplus = net10+net40; E surplus = net10; hence all equal N>0.')
print('Conditional only: actual branching and all-mass sector presentation not certified here.')

# Match the Lean literal profiles independently to the full character result.
lean = (root / 'GUT/SU5/SelectionRules/ExoticCopyIndexBounds.lean').read_text()
line = next(l for l in lean.splitlines() if l.startswith('def profiles'))
literal = ast.literal_eval(line.split(':= !',1)[1])
assert [Counter(v) for v in literal] == [Counter(branches[n]) for n in chars]
print('Lean literal profiles match the complete-character decomposition.')
