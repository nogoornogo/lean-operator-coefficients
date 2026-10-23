#!/usr/bin/env python3
"""Exact finite C5 diagnostic in dual-Pauli direction coordinates.

The ordered exterior/polynomial monomials and Lie/EOM/IBP rows are an
independent rational model. Their map to the Lean selected source and the
full unbounded relation preimage has NOT been proved. Counts here are
not actual-input completeness theorems or Lean premises.
"""
from itertools import combinations, combinations_with_replacement, product
from fractions import Fraction as Q
from collections import defaultdict
import json
ODD = [(f,-1) for f in range(4)]
BOS4 = list(combinations_with_replacement(range(4),4))
BOS3 = list(combinations_with_replacement(range(4),3))
def canon(o,e):
 if len(set(o)) < len(o): return 0,None
 sign=(-1)**sum(o[i]>o[j] for i in range(len(o)) for j in range(i+1,len(o)))
 return sign,(tuple(sorted(o)),tuple(sorted(e)))
def charge(m):
 o,e=m
 return sum(2 if f<2 else -2 for f,d in o)+sum(1 if f<2 else -1 for f,d in e)
def weight(m):
 ans=[0,0,0]
 for odd,ls in [(True,m[0]),(False,m[1])]:
  for f,d in ls:
   if odd: ans[f//2] += 1 if f%2==0 else -1
   else: ans[2] += [1,-1,-1,1][f]
   if d>=0:
    a,b=divmod(d,2);ans[0]-=1 if a==0 else -1;ans[1]-=1 if b==0 else -1
 return tuple(ans)
raw=[]
for os in combinations(ODD,2):
 for bs in BOS3:
  for f,d in product(range(4),range(4)):
   raw.append(canon(os,[(b,-1) for b in bs]+[(f,d)])[1])
for f,g,d in product(range(4),range(4),range(4)):
 for bs in BOS4: raw.append(canon([(f,-1),(g,d)],[(b,-1) for b in bs])[1])
assert len(set(raw))==4160
balanced=[m for m in raw if charge(m)==0]
zero=[m for m in balanced if weight(m)==(0,0,0)]
ids={m:i for i,m in enumerate(zero)}
def addterm(row,c,o,e):
 s,m=canon(o,e)
 if s and m in ids: row[ids[m]]+=s*c

def lie(m,k,up):
 row=defaultdict(int)
 for odd,pos in [(True,0),(False,1)]:
  for j,(f,d) in enumerate(m[pos]):
   ts=[]
   if odd and f//2==k and k<2:
    if f%2==(1 if up else 0): ts.append((1,(f-1 if up else f+1,d)))
   if not odd and k==2:
    if (f,up) in [(1,True),(0,False)]:ts.append((1,(1-f,d)))
    if (f,up) in [(2,True),(3,False)]:ts.append((-1,(5-f,d)))
   if d>=0 and k<2:
    a,b=divmod(d,2);v=[a,b]
    if v[k]==(0 if up else 1):
     v[k]=1-v[k];ts.append((-1,(f,2*v[0]+v[1])))
   for c,t in ts:
    ls=[list(m[0]),list(m[1])];ls[pos][j]=t;addterm(row,c,*ls)
 return {i:v for i,v in row.items() if v}
rows=[]
for m in balanced:
 for k,up in product(range(3),[False,True]):
  r=lie(m,k,up)
  if r:rows.append(r)
lie_count=len(rows)
# Both Weyl equations, multiplied by every zero-order odd field and quartic boson monomial.
for right,a,f,bs in product([False,True],range(2),range(4),BOS4):
 r=defaultdict(int)
 for b in range(2):
  spinor=2+b if right else b
  d=2*a+b if right else 2*b+a
  addterm(r,1,[(spinor,d),(f,-1)],[(x,-1) for x in bs])
 if r:rows.append(dict(r))
eom_count=len(rows)-lie_count
for os,bs,d in product(combinations(ODD,2),BOS4,range(4)):
 r=defaultdict(int);es=[(x,-1) for x in bs]
 for pos in range(2):
  o=list(os);o[pos]=(o[pos][0],d);addterm(r,1,o,es)
 for pos in range(4):
  e=es.copy();e[pos]=(e[pos][0],d);addterm(r,1,os,e)
 if r:rows.append(dict(r))
ibp_count=len(rows)-lie_count-eom_count

def eliminate(rs):
 piv={}
 for rawrow in rs:
  r={i:Q(v) for i,v in rawrow.items() if v}
  while r:
   p=min(r);c=r[p]
   if p not in piv:
    piv[p]={i:v/c for i,v in r.items()};break
   for i,v in piv[p].items():
    z=r.get(i,Q(0))-c*v
    if z:r[i]=z
    else:r.pop(i,None)
 return piv
ranks=[len(eliminate(rows[:n])) for n in [lie_count,lie_count+eom_count,len(rows)]]
piv=eliminate(rows);free=[i for i in range(len(zero)) if i not in piv]
assert len(free)==1
f={free[0]:Q(1)}
for i,row in sorted(piv.items(),reverse=True): f[i]=-sum(v*f.get(j,Q(0)) for j,v in row.items() if j!=i)
# Pauli current contracted with Dmatrix_ab on H/Hdag, times rho; factor i omitted.
candidate=defaultdict(int)
for a,b,c,e in product(range(2),range(2),range(2),range(2)):
 o=[(a,-1),(2+b,-1)];d=2*a+b
 addterm(candidate,1,o,[(2+c,-1),(c,d),(2+e,-1),(e,-1)])
 addterm(candidate,-1,o,[(2+c,d),(c,-1),(2+e,-1),(e,-1)])
value=sum(v*f[i] for i,v in candidate.items())
assert value==24
assert all(sum(Q(v)*f.get(i,Q(0)) for i,v in row.items())==0 for row in rows)
# Independent omission controls: both equation families and IBP matter.
without_eom = len(zero)-len(eliminate(rows[:lie_count]+rows[lie_count+eom_count:]))
without_ibp = len(zero)-ranks[1]
assert without_eom==3 and without_ibp==2
symmetric=defaultdict(int)
for a,b,c,e in product(range(2),range(2),range(2),range(2)):
 o=[(a,-1),(2+b,-1)];d=2*a+b
 addterm(symmetric,1,o,[(2+c,-1),(c,d),(2+e,-1),(e,-1)])
 addterm(symmetric,1,o,[(2+c,d),(c,-1),(2+e,-1),(e,-1)])
assert sum(v*f[i] for i,v in symmetric.items())==0
print(json.dumps(dict(role='exact finite diagnostic only; no Lean source bridge',raw=4160,
 hypercharge_zero=len(balanced),cartan_zero=len(zero),rows=[lie_count,eom_count,ibp_count],
 ranks=ranks,remaining=len(free),candidate=str(value),without_weyl_eom=without_eom,without_ibp=without_ibp,
 symmetric_current="zero",all_row_residuals="zero"),indent=2))
