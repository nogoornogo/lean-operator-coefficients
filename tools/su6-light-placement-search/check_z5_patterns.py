"""Exact 125-case charge search; supplied charge conditions, not UV models."""
from itertools import product


def scan():
    accepted=[]
    for x,y,h in product(range(5),repeat=3):
        u,d,e=(-x-h)%5,(-x+h)%5,(-y+h)%5
        assert (x+u+h)%5 == (x+d-h)%5 == (y+e-h)%5 == 0
        qque=(2*x-u-e)%5
        assert qque == (3*x+y)%5
        # Other familiar dimension-six baryon charges agree on these inputs.
        assert (3*x+y)%5 == (-d-u+x+y)%5 == (-2*u-d-e)%5
        llhh=2*(y+h)%5
        if qque and not llhh:
            accepted.append((x,u,d,y,e,h))
    assert len(accepted)==20
    assert sum(h==0 for _,_,_,_,_,h in accepted)==4
    assert (1,4,4,0,0,0) in accepted
    assert (0,0,0,0,0,0) not in accepted
    # Charges of selected Q/U/E cannot have the prior scalar/block cancellation.
    assert all((2*q-u-e)%5 != 0 for q,u,_,_,e,_ in accepted)
    print('125 triples; 20 mixed-charge matches, 4 neutral-Higgs and 16 charged-Higgs')
    print('witness (Q,U,D,L,E,H) = (1,4,4,0,0,0)')
    print('No UV covariance, anomaly cancellation, or physical carrier admission certified')


if __name__ == '__main__':
    scan()
