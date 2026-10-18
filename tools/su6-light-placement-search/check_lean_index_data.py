"""Check supplied Lean inputs against the independent complete-character screen.
Functionals and targets are derived here, not parsed from evaluated tables.
Lean verifies their structural derivation; this script is not its premise.
"""
import ast
from collections import Counter
from pathlib import Path
import check_small_branching as b

ROOT=Path(__file__).resolve().parents[2]
source=(ROOT/'GUT/SU6/SelectionRules/Models/FiniteIndexCertificate.lean').read_text()

def data(name):
    line=next(line for line in source.splitlines() if line.startswith(f'def {name} :'))
    return ast.literal_eval(line.split(':=',1)[1].strip().replace('![','['))

def main():
    branches,rows,lights=(data(n) for n in ('branching','rows','lightProfile'))
    assert len(rows)==len(set(rows))==7
    def functional(terms):
        assert all(row in rows for row,_ in terms)
        return [sum(weight for row,weight in terms if row==selected) for selected in rows]
    lepton=(0,0,1,-3);down=(0,1,0,2)
    difference=functional([((0,lepton),1),((0,down),-1)])
    balance=functional([((0,(0,1,0,-4)),1),((0,(0,1,1,-1)),1),((0,(2,0,0,-4)),1)])
    charged=functional([((1,lepton),-1),((1,down),1)])
    negate=lambda v:[-x for x in v]
    certs=[negate(balance),charged,difference,negate(difference),balance]
    unit=Counter({(0,0,0,0):1});f=Counter(b.F)
    chars=[unit,f,b.exterior(2),b.exterior(3),b.symmetric(2),
           b.difference(b.tensor(f,b.negate(f)),unit),
           b.difference(b.tensor(f,b.exterior(2)),b.exterior(3))]
    assert len(branches)==7
    for branch,char in zip(branches,chars): assert Counter(branch)==Counter(b.decompose(char))
    conj=lambda g:(g[1],g[0],g[2],-g[3])
    for x in range(5):
        y,h=(1-3*x)%5,(3*x-1)%5
        expected=[(x,(1,0,1,1)),((-x-h)%5,(0,1,0,-4)),
                  ((-x+h)%5,(0,1,0,2)),(y,(0,0,1,-3)),((-y+h)%5,(0,0,0,6))]
        assert lights[x]==expected
        target=[lights[x].count((q,g))-lights[x].count(((-q)%5,conj(g))) for q,g in rows]
        for branch in branches:
            for charge in range(5):
                col=[(branch.count(g) if q==charge else 0)-
                     (branch.count(conj(g)) if q==(-charge)%5 else 0) for q,g in rows]
                assert sum(a*z for a,z in zip(certs[x],col))==0
        assert sum(a*z for a,z in zip(certs[x],target))==1
    print('Static Lean branch/row/light inputs agree with complete-character screen; independently derived functionals check 175 column and 5 separation identities')

if __name__=='__main__': main()
