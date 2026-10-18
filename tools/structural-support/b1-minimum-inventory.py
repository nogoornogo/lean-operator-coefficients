#!/usr/bin/env python3
"""Diagnostic B1 dimension intervals; not a theorem input or search oracle.

Reads existing Lean witness syntax, lists the unchanged 572 assignment domain,
and proposes intervals for its 326 all-degree-allowed rows. Uses only Python's
standard library. --rows prints the complete inventory; default prints summary.
"""
import argparse
import collections
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def existing_templates():
    text = (ROOT/'Physics/StandardModel/Operators/SMLeptonChargeWitnesses.lean').read_text()
    result = []
    for sign, a, n in re.findall(r'def w3_([np])(\d+)_pattern \(i : Fin (\d+)\)', text):
        tag = 'w3_'+sign+a
        match = re.search(r'theorem '+tag+r'_exact[\s\S]*?refine ⟨\d+, '+tag+r'_pattern, (\d+), (\d+),', text)
        if match is None:
            raise ValueError('missing exact witness '+tag)
        h, d = map(int, match.groups())
        z = int(a) * (-1 if sign == 'n' else 1)
        result.append(dict(tag=tag, L=z, n=int(n), h=h, d=d, M=3*int(n)+2*(h+d)))
    if len(result) != 18:
        raise ValueError('expected exactly 18 existing B1 families')
    result.extend(dict(tag=t,L=z,n=n,h=h,d=d,M=3*n+2*(h+d)) for t,z,n,h,d in
                  [('c1',1,4,0,0),('h1',3,6,0,0),('h2',-3,6,0,1)])
    return result


def lower(z):
    n = 3+abs(z)
    return max(3*n, n+2*abs(2*z-1))


def refined_lower(z):
    raw=max(lower(z),7*z-15,-7*z-9)
    return raw if (raw+z-1)%4==0 else raw+2


def inventory(templates, lower_function=lower):
    out=[]
    for k in range(2,13):
        for q in range(k):
            for l in range(k):
                if (3*q+l)%k == 0:
                    continue
                neutral=[z for z in range(-17,18,2) if (3*q+z*l)%k == 0]
                if not neutral:
                    continue
                lo=min(lower_function(z) for z in neutral)
                live=[t for t in templates if t['L'] in neutral]
                best=min(live,key=lambda t:(t['M'],t['tag']))
                out.append(dict(k=k,q=q,l=l,neutral=neutral,lower=lo,upper=best['M'],
                                witness=best['tag'],exact=lo==best['M']))
    if len(out)!=326:
        raise ValueError('all-degree-allowed domain changed')
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rows',action='store_true')
    modes=parser.add_mutually_exclusive_group()
    modes.add_argument('--refined',action='store_true',help='UNVERIFIED weak/chirality lower-bound proposal; never a proved result')
    modes.add_argument('--retained',action='store_true',help='retained charge/cutoff bounds and kernel-certified witness grades')
    args=parser.parse_args()
    templates=existing_templates()
    if args.refined or args.retained:
        replacements=[(5,8,2,0),(-5,8,0,3),(7,10,4,0),(-7,10,0,5),(9,14,3,0),(-9,16,0,3),(11,20,1,0),(-11,22,0,1)]
        templates.extend(dict(tag=('new_p' if z>0 else 'new_n')+str(abs(z)),L=z,n=n,h=h,d=d,M=3*n+2*(h+d)) for z,n,h,d in replacements)
    rows=inventory(templates,refined_lower if args.refined else lower)
    if args.retained:
        for r in rows:
            cheap=any((3*r['q']+z*r['l'])%r['k']==0 for z in (1,-1,3))
            r['lower']=max(3*(3+min(map(abs,r['neutral']))),0 if cheap else 20)
            r['exact']=r['lower']==r['upper']
    summary=dict(diagnostic_only=True,mode="unverified-refined" if args.refined else "retained" if args.retained else "initial",templates=templates,allowed_rows=len(rows),
                 matching=sum(r['exact'] for r in rows),unresolved=sum(not r['exact'] for r in rows),
                 maximum_upper=max(r['upper'] for r in rows),
                 maximum_gap=max(r['upper']-r['lower'] for r in rows),
                 lower_distribution=dict(sorted(collections.Counter(r['lower'] for r in rows).items())),
                 gaps=[dict(lower=a,upper=b,count=c) for (a,b),c in
                       sorted(collections.Counter((r['lower'],r['upper']) for r in rows).items())])
    if args.rows:
        summary['rows']=rows
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    main()
