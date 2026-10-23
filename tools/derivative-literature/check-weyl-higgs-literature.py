#!/usr/bin/env python3
"""Native C5 current dictionaries over exact Gaussian rationals and an exterior algebra.

Independent diagnostics only. Printed density agreement does not establish
completeness of the actual Lean selected coefficient space.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
import json

@dataclass(frozen=True)
class C:
    re: Q = Q(0)
    im: Q = Q(0)
    def __add__(self, other):
        other = as_c(other)
        return C(self.re+other.re, self.im+other.im)
    __radd__ = __add__
    def __neg__(self): return C(-self.re, -self.im)
    def __sub__(self, other): return self+-as_c(other)
    def __rsub__(self, other): return as_c(other)+-self
    def __mul__(self, other):
        other = as_c(other)
        return C(self.re*other.re-self.im*other.im,
                 self.re*other.im+self.im*other.re)
    __rmul__ = __mul__
    def conj(self): return C(self.re, -self.im)

def as_c(x): return x if isinstance(x,C) else C(Q(x))
Z, O, I = C(), C(Q(1)), C(Q(0),Q(1))
SIGMA = [((O,Z),(Z,O)), ((Z,O),(O,Z)), ((Z,-I),(I,Z)), ((O,Z),(Z,-O))]
ETA = (1,-1,-1,-1)
def multiply(a,b):
    n=len(a)
    return tuple(tuple(sum((a[i][k]*b[k][j] for k in range(n)),Z)
                       for j in range(n)) for i in range(n))
def identity(n): return tuple(tuple(O if i==j else Z for j in range(n)) for i in range(n))
def gamma(mu):
    return tuple(tuple(Z if a//2==b//2 else
                       SIGMA[mu][a%2][b%2]*(ETA[mu] if a//2 else 1)
                       for b in range(4)) for a in range(4))
PR = tuple(tuple(O if a==b and a>=2 else Z for b in range(4)) for a in range(4))

def add(*ps):
    ans={}
    for p in ps:
        for k,v in p.items():ans[k]=ans.get(k,Z)+v
    return {k:v for k,v in ans.items() if v!=Z}
def scale(c,p):return {k:v*as_c(c) for k,v in p.items() if v*as_c(c)!=Z}
def wedge(p,q):
    ans={}
    for a,x in p.items():
        for b,y in q.items():
            if a & b:continue
            sign=(-1)**sum((b & ((1<<i)-1)).bit_count() for i in range(8) if a & (1<<i))
            key=a|b;ans[key]=ans.get(key,Z)+sign*x*y
    return {k:v for k,v in ans.items() if v!=Z}
def v(i):return {1<<i:O}
def pauli_current(mu):
    return add(*(scale(SIGMA[mu][a][b],wedge(v(a),v(2+b))) for a,b in product(range(2),repeat=2)))
def four_current(mu):
    # Psi=(chi,eta dagger), barPsi=(eta,chi dagger), all eight odd variables independent.
    psi=[v(4),v(5),v(2),v(3)];bar=[v(0),v(1),v(6),v(7)]
    m=multiply(gamma(mu),PR)
    return add(*(scale(m[a][b],wedge(bar[a],psi[b])) for a,b in product(range(4),repeat=2)))
def reverse_current(mu):
    raised_eta=[v(1),scale(-1,v(0))];raised_dagger=[v(3),scale(-1,v(2))]
    return add(*(scale(ETA[mu]*SIGMA[mu][a][b],wedge(raised_dagger[a],raised_eta[b]))
                 for a,b in product(range(2),repeat=2)))

def configurations():
    for k in range(1,9):
        h=[C(Q(k,3),Q(1-k,5)),C(Q(2-k,7),Q(k,11))]
        hb=[z.conj() for z in h]
        dh=[[C(Q(k+i+a,5),Q(i-a,7)) for a in range(2)] for i in range(4)]
        dhb=[[z.conj() for z in row] for row in dh]
        rho=sum((hb[a]*h[a] for a in range(2)),Z)
        current=[sum((hb[a]*dh[i][a]-dhb[i][a]*h[a] for a in range(2)),Z) for i in range(4)]
        yield rho,current

def li(factor=1):
    count=0
    for rho,hc in configurations():
        literal=add(*(scale(I*hc[mu]*rho,pauli_current(mu)) for mu in range(4)))
        native=add(*(scale(factor*I*hc[mu]*rho,pauli_current(mu)) for mu in range(4)))
        assert native==literal, 'Li Eq. (4.24) overall factor differs'
        assert literal and scale(-1,literal)!=literal
        count+=1
    return dict(checks=count,scope='ordered native density; completeness not certified')
def murphy():
    for mu in range(4):assert four_current(mu)==pauli_current(mu)
    count=0
    for rho,hc in configurations():
        assert add(*(scale(I*hc[mu]*rho,four_current(mu)) for mu in range(4)))== \
               add(*(scale(I*hc[mu]*rho,pauli_current(mu)) for mu in range(4)))
        count+=1
    return dict(checks=count,block_component_checks=4,scope='right-chiral one-flavor density')
def dhm():
    for mu,nu in product(range(4),repeat=2):
        a=multiply(gamma(mu),gamma(nu));b=multiply(gamma(nu),gamma(mu))
        target=tuple(tuple(as_c(2*ETA[mu] if mu==nu and i==j else 0) for j in range(4)) for i in range(4))
        assert tuple(tuple(a[i][j]+b[i][j] for j in range(4)) for i in range(4))==target
    for mu in range(4):
        assert four_current(mu)==pauli_current(mu)==scale(-1,reverse_current(mu))
        assert pauli_current(mu)!=reverse_current(mu), 'missing Grassmann minus not detected'
    return dict(clifford_pairs=16,block_and_reversal_checks=4,scope='G.1.82 and footnote 127')
def queue(li_factor=1):
    results=[]
    for paper,check in [('Li 2005.00008v3 Eq. (4.24)',lambda:li(li_factor)),
                        ('Murphy 2005.00059v6 Table 5',murphy),
                        ('Dreiner-Haber-Martin 0812.1594v6 G.1.82',dhm)]:
        try:results.append(dict(paper=paper,status='agreement',**check()))
        except (AssertionError,ArithmeticError) as exc:
            results.append(dict(paper=paper,status='discrepancy',detail=str(exc)))
    return results

def main():
    actual=queue();control=queue(2)
    assert [r['status'] for r in control]==['discrepancy','agreement','agreement']
    print(json.dumps(dict(role='exact diagnostic, not a Lean premise',papers=actual,
                         continuation_control=control),indent=2))
    return int(any(r['status']!='agreement' for r in actual))
if __name__=='__main__':raise SystemExit(main())
