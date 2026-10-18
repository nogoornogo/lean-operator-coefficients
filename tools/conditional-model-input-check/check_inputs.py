#!/usr/bin/env python3
"""Exact charge/VEV convention controls, standard library only.
These checks do not prove carrier identifications, UV matching or actual
coefficient existence. The independently kernel-checked Lean files do that
only on their declared input domains.
"""
from fractions import Fraction


def dlt(m, p):
    # Physical Q,uR,dR,L,eR,Hu,Hd; n=0 in Eq.(2.17).
    return (0, m, -m, -p, -m-p, m, -m)


def main():
    # DFPW: b=6B,l=2L; VEVs (-18,-6),(0,-4).
    stabilizer = [(k, j) for k in range(36) for j in range(4)
                  if (k+3*j) % 2 == 0]
    assert len(stabilizer) == 72
    for k, j in stabilizer:
        x, y = Fraction(k, 36), Fraction(j, 4)
        assert (-18*x-6*y).denominator == 1
        assert (-4*y).denominator == 1
    assert (2, 0) in stabilizer  # x=1/18,y=0
    assert 3*2 % 18 == 6 and 6*2 % 18 == 12
    # X=3(B-L): physical species charges and charge-two breaking singlet.
    xcharges = (1, 1, 1, -3, -3)
    assert (3*xcharges[0]+xcharges[4]) == 0  # qque, even before breaking
    assert 6*xcharges[0] % 6 == 0 and 2*xcharges[3] % 6 == 0
    assert 6*xcharges[0] % 5 != 0 and 2*xcharges[3] % 5 != 0
    bgw = (0, 1, -1, 2, 1, 1, -1)
    b3 = dlt(1, 1)
    p6 = dlt(5, 2)
    assert all((a-b) % 3 == 0 for a, b in zip(bgw, b3))
    assert all((a+b) % 6 == 0 for a, b in zip(bgw, p6))
    for charges, modulus in ((b3, 3), (p6, 6)):
        q, u, d, l, e, hu, hd = charges
        assert (2*q+u+e) % modulus != 0
        assert (2*u+4*d) % modulus != 0
        assert (2*l+2*hu) % modulus == 0
        assert (hu+hd) % modulus == 0
        assert hu % modulus != 0  # reject the neutral-Higgs shortcut
    # Ma: L,ec,H even; eta and N odd. This is only a parity control.
    assert (0+1+1) % 2 == 0   # L eta N
    assert (0+0+1) % 2 != 0   # L H N
    assert (2*0+2*0) % 2 == 0 # LLHH
    print('PASS: DFPW 72 cover elements; B-L charge controls; B3/P6 dictionaries and charged Higgs; Ma parity controls')


if __name__ == '__main__':
    main()
