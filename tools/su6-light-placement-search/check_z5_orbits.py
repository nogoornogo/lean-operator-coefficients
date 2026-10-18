"""Exact generator-change quotient and fixed SU6 phase screen; not UV models."""
from itertools import product
from check_z5_patterns import scan


def fields(x,y,h):
    return (x,(-x-h)%5,(-x+h)%5,y,(-y+h)%5,h)


def baryon(v):
    q,u,_,_,e,_=v
    return (2*q-u-e)%5


def scale(v,k):
    return tuple(k*x%5 for x in v)


def main():
    scan()  # Recheck original census and controls.
    accepted={fields(x,y,h) for x,y,h in product(range(5),repeat=3)
              if (3*x+y)%5 and 2*(y+h)%5==0}
    orbits={frozenset(scale(v,k) for k in range(1,5)) for v in accepted}
    assert len(orbits)==5
    assert all(len(o)==4 and o<=accepted for o in orbits)
    assert set().union(*orbits)==accepted
    reps=sorted(scale(v,pow(baryon(v),-1,5)) for v in accepted)
    reps=sorted(set(reps))
    assert len(reps)==5
    assert all(baryon(v)==1 for v in reps)
    assert all(sum(baryon(v)==1 for v in o)==1 for o in orbits)
    # Standard scalar/block phases on the fifteen; no homomorphic UV lift
    # assumed. All variables are pointwise Z5 phases.
    blocks=[((a+c+w)%5,(a+2*c)%5,(a+2*w)%5)
            for a,c,w,t in product(range(5),repeat=4) if (3*c+2*w+t)%5==0]
    assert len(blocks)==125
    assert all((2*q-u-e)%5==0 for q,u,e in blocks)
    for v in reps:
        q,u,_,_,e,_=v
        matches=sum((q,u,e)==b for b in blocks)
        assert matches==0
        print(f'representative Q,U,D,L,E,H={v}: qque=1; scalar/block SU6 fits={matches}')
    # Separate, explicitly labelled gauge-dressing comparison, not a UV
    # model isomorphism. 6Y=(1,-4,2,-3,6,3), reduced modulo five.
    hyper=(1,1,2,2,1,3)
    dressed={tuple((v+s*y)%5 for v,y in zip(reps[0],hyper)) for s in range(5)}
    assert dressed==set(reps)
    print('All five normalized representatives are related by hypercharge dressing at charge level')
    assert (0,0,0) in blocks  # Positive fitting control, not a protecting input.
    print('20 assignments -> 5 generator orbits; all 5 reject the fixed scalar/block SU6 gate')
    print('No broader UV or physical equivalence inferred')


if __name__ == '__main__':
    main()
