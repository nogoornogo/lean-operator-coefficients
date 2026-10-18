"""Exact integer/rational cross-check of the 25-coordinate species quotient.

No physical simulation or trusted proof oracle: Lean separately checks the
permutation identities and the resulting linear deductions. Uses only the
Python standard library; changes no dependencies.
Run: python tools/delta-b-two/species-quotient.py
"""
from fractions import Fraction as F
import sys

CP = [(0,1,2,0,1,2), (0,1,0,2,1,2), (0,1,0,1,2,2),
      (0,0,1,2,1,2), (0,0,1,1,2,2)]
SP = [(0,1,0,1,0,1), (0,1,0,0,1,1), (0,0,1,1,0,1),
      (0,0,1,0,1,1), (0,0,0,1,1,1)]
CI = [[1,0,0,0,-1], [0,1,0,0,0], [0,0,1,0,0],
      [0,0,0,1,0], [0,0,0,0,1]]
SI = [[1,1,1,1,2], [0,1,0,1,1], [0,0,1,1,1],
      [0,0,0,1,1], [0,0,0,0,1]]
CT = [(0,1,2,3,4,5), (0,1,3,2,4,5), (0,1,4,2,3,5),
      (0,2,3,1,4,5), (0,2,4,1,3,5)]
ST = [(0,1,2,3,4,5), (0,1,2,5,3,4), (0,3,1,2,4,5),
      (0,5,1,2,3,4), (0,5,1,4,2,3)]
SWAPS = [(0,2), (1,3), (3,4), (4,5)]

def eps(xs):
    if len(set(xs)) != len(xs):
        return 0
    return (-1) ** sum(xs[i] > xs[j] for i in range(len(xs))
                        for j in range(i+1,len(xs)))

def color(p, x):
    t = CT[p]
    return eps(tuple(x[i] for i in t[:3])) * eps(tuple(x[i] for i in t[3:]))

def spin(p, x):
    t = ST[p]
    return eps((x[t[0]],x[t[1]])) * eps((x[t[2]],x[t[3]])) * eps((x[t[4]],x[t[5]]))

def swapped(x, pair):
    y = list(x)
    a,b = pair
    y[a],y[b] = y[b],y[a]
    return y

def main():
    if '--lean-words' in sys.argv:
        words = {tuple(range(6)): []}
        queue = list(words)
        for p in queue:
            for g, (a, b) in enumerate(SWAPS):
                q = tuple(b if x == a else a if x == b else x for x in p)
                if q not in words:
                    words[q] = [g] + words[p]
                    queue.append(q)
        assert len(words) == 48
        print('private def generatorWords : Fin 48 → List (Fin 4) := ![')
        print(',\n'.join('  [' + ', '.join(map(str, w)) + ']' for w in words.values()) + ']')
        return
    rows = []
    for pair in SWAPS:
        a = [[sum(CI[i][j]*color(p,swapped(CP[j],pair)) for j in range(5))
              for p in range(5)] for i in range(5)]
        b = [[sum(SI[i][j]*spin(p,swapped(SP[j],pair)) for j in range(5))
              for p in range(5)] for i in range(5)]
        if '--lean-proof' not in sys.argv:
            print('swap', pair, 'color', a, 'spin', b)
        rows += [[int(i==j) + a[i//5][j//5]*b[i%5][j%5]
                  for j in range(25)] for i in range(25)]
    rr = [[F(x) for x in row] + [F(i==j) for j in range(100)]
          for i,row in enumerate(rows)]
    pivots = []
    for col in range(25):
        n = len(pivots)
        candidates = [i for i in range(n,100) if rr[i][col]]
        pivot = min(candidates, key=lambda i: sum(x != 0 for x in rr[i]),
                    default=None)
        if pivot is None:
            continue
        rr[n],rr[pivot] = rr[pivot],rr[n]
        factor = rr[n][col]
        rr[n] = [x/factor for x in rr[n]]
        for i in range(100):
            if i != n and rr[i][col]:
                factor = rr[i][col]
                rr[i] = [x-factor*y for x,y in zip(rr[i],rr[n])]
        pivots.append(col)
    if '--lean-proof' not in sys.argv:
        print('rank',len(pivots),'free',[i for i in range(25) if i not in pivots])
    free = [i for i in range(25) if i not in pivots]
    nullspace = []
    for i in free:
        v = [F(j==i) for j in range(25)]
        for n,col in enumerate(pivots):
            v[col] = -rr[n][i]
        nullspace.append(v)
    if '--lean-proof' not in sys.argv:
        print('nullspace',[[str(x) for x in v] for v in nullspace])
    # Keep a sparse row certificate for each reconstructed coordinate.
    certificates = {}
    for n,col in enumerate(pivots):
        cert = [(i,str(rr[n][25+i])) for i in range(100) if rr[n][25+i]]
        certificates[col] = cert
        if '--lean-proof' not in sys.argv:
            print('certificate',col,cert)
    assert len(pivots) == 23
    if '--lean-proof' in sys.argv:
        print('''/-- The isolated 25-coordinate linear deduction. Each normalization
checks a sparse rational row certificate; no external rank premise is used. -/
theorem kernel_reconstruct (c : Fin 5 → Fin 5 → ℂ) (h : SatisfiesStatistics c) :
    c = embed ![c 4 0, c 4 2] := by
  ext p q
  fin_cases p <;> fin_cases q''')
        for col in range(25):
            if col in free:
                print('  next => rfl')
            else:
                terms = []
                for i,v in certificates[col]:
                    weight = F(v)
                    value = f'({weight.numerator} / {weight.denominator} : ℂ)' if weight.denominator != 1 else f'({weight.numerator} : ℂ)'
                    terms.append(f'{value} * (h {i//25} {(i%25)//5} {i%5})')
                finish = '' if col in {11, 13, 15, 17, 19, 21, 23, 24} else '; ring'
                print('  next =>\n    linear_combination (norm := (simp [residual, embed, colorMatrix,\n      spinMatrix, Fin.sum_univ_succ]' + finish + ')) ' + ' + '.join(terms))

if __name__ == '__main__':
    main()
