"""Exact character decomposition screen, not Lean branching equivalences."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, product

F=[(1,0,0,-2),(-1,1,0,-2),(0,-1,0,-2),(0,0,1,3),(0,0,-1,3),(0,0,0,0)]

def add(a,b): return tuple(x+y for x,y in zip(a,b))
def tensor(a,b):
    c=Counter()
    for x,n in a.items():
        for y,m in b.items(): c[add(x,y)]+=n*m
    return c

def negate(c): return Counter({tuple(-x for x in w):n for w,n in c.items()})
def difference(a,b):
    c=a.copy()
    for w,n in b.items(): c[w]-=n
    assert all(n>=0 for n in c.values())
    return Counter({w:n for w,n in c.items() if n})

def sums(weights,selections):
    c=Counter()
    for ids in selections:
        w=(0,)*len(weights[0])
        for i in ids: w=add(w,weights[i])
        c[w]+=1
    return c

def exterior(k): return sums(F,combinations(range(6),k))
def symmetric(k): return sums(F,combinations_with_replacement(range(6),k))

def color(p,q):
    f=[(1,0),(-1,1),(0,-1)]
    sf=lambda n: sums(f,combinations_with_replacement(range(3),n))
    a=tensor(sf(p),negate(sf(q)))
    return difference(a,tensor(sf(p-1),negate(sf(q-1)))) if p and q else a

def irrep(p,q,n,y):
    return Counter({(a,b,w,y):k for (a,b),k in color(p,q).items()
                    for w in range(n,-n-1,-2)})

def decompose(c):
    remainder=c.copy(); out=[]
    while remainder:
        dominant=[w for w in remainder if w[0]>=0 and w[1]>=0 and w[2]>=0]
        assert dominant
        # Strictly positive on both color simple roots and the weak root.
        p,q,n,y=max(dominant,key=lambda w:(2*w[0]+2*w[1]+w[2],w))
        m=remainder[(p,q,n,y)]
        block=irrep(p,q,n,y)
        remainder=difference(remainder,Counter({w:k*m for w,k in block.items()}))
        out.append(((p,q,n,y),m))
    return dict(out)


def main():
    unit=Counter({(0,0,0,0):1}); fund=Counter(F)
    chars={'1':unit,'6':fund,'15':exterior(2),'20':exterior(3),
           '21':symmetric(2),'35':difference(tensor(fund,negate(fund)),unit),
           '70':difference(tensor(fund,exterior(2)),exterior(3))}
    targets={'Q':(1,0,1,1),'U':(0,1,0,-4),'E':(0,0,0,6)}
    expected={'1':(0,0,0),'6':(0,0,0),'15':(1,1,1),'20':(1,1,1),
              '21':(1,0,0),'35':(0,0,0),'70':(2,1,1)}
    branches={}
    for name,c in chars.items():
        assert sum(c.values())==int(name)
        d=decompose(c)
        branches[name]=d
        rebuilt=Counter()
        for (p,q,n,y),m in d.items():
            rebuilt.update({w:k*m for w,k in irrep(p,q,n,y).items()})
        assert rebuilt==c
        counts=tuple(d.get(t,0) for t in targets.values())
        assert counts==expected[name],(name,counts)
        print(name,'Q,U,E copies:',counts,'blocks:',sorted(d.items()))
        dc=decompose(negate(c))
        print('conjugate',name,'Q,U,E:',tuple(dc.get(t,0) for t in targets.values()))
    # Necessary charge-resolved chiral-index equation. Pairing by an
    # invariant symmetric mass removes R@q together with conjugate R@-q.
    # Rational span is a relaxation of nonnegative integral multiplicities.
    from fractions import Fraction
    conjugate=lambda g:(g[1],g[0],g[2],-g[3])
    keys=sorted({(q,g) for q in range(5) for d in branches.values()
                 for g in list(d)+[conjugate(g) for g in d]})
    def index_column(d,q):
        c=Counter()
        for g,n in d.items():
            c[(q,g)]+=n
            c[((-q)%5,conjugate(g))]-=n
        return [c[k] for k in keys]
    columns=[index_column(d,q) for d in branches.values() for q in range(5)]
    neutral=Counter()
    for g in [(1,0,1,1),(0,1,0,-4),(0,1,0,2),(0,0,1,-3),(0,0,0,6)]:
        neutral[(0,g)]+=1
        neutral[(0,conjugate(g))]-=1
    c15=index_column(branches['15'],0); c6=index_column(branches['6'],0)
    assert [c15[i]-2*c6[i] for i in range(len(keys))]==[neutral[k] for k in keys]
    print('Positive index control: neutral SM target = 15 - 2*6 index')
    for x in range(5):
        y,h=(1-3*x)%5,(3*x-1)%5
        u,d,e=(-x-h)%5,(-x+h)%5,(-y+h)%5
        target=Counter()
        for g,q in [((1,0,1,1),x),((0,1,0,-4),u),((0,1,0,2),d),
                    ((0,0,1,-3),y),((0,0,0,6),e)]:
            target[(q,g)]+=1
            target[((-q)%5,conjugate(g))]-=1
        assert set(target)<=set(keys)
        rows=[[Fraction(col[i]) for col in columns]+[Fraction(target[k])]
              for i,k in enumerate(keys)]
        pivot=0
        for j in range(len(columns)):
            i=next((i for i in range(pivot,len(rows)) if rows[i][j]),None)
            if i is None: continue
            rows[pivot],rows[i]=rows[i],rows[pivot]
            z=rows[pivot][j]; rows[pivot]=[v/z for v in rows[pivot]]
            for i in range(len(rows)):
                if i!=pivot and rows[i][j]:
                    z=rows[i][j]; rows[i]=[v-z*w for v,w in zip(rows[i],rows[pivot])]
            pivot+=1
        inconsistent=any(not any(row[:-1]) and row[-1] for row in rows)
        print(f'Exact SM target x={x}: coefficient rank={pivot}, inconsistent={inconsistent}')
        assert inconsistent
    print('Exact complete-character subtraction/reconstruction passed; no UV mass or Lean bridge inferred')


if __name__=='__main__': main()
