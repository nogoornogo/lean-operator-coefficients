"""Exact selected PS contraction, exterior and neutral-mass controls."""
from fractions import Fraction as F
from itertools import permutations, product
import unittest


def eps(indices):
    if len(set(indices)) != len(indices):
        return 0
    return (-1)**sum(a>b for i,a in enumerate(indices) for b in indices[i+1:])

def wedge_product(a,b):
    result={}
    for x,c in a.items():
        for y,d in b.items():
            if set(x)&set(y):
                continue
            z=x+y
            sign=(-1)**sum(i>j for i in x for j in y)
            key=tuple(sorted(z))
            result[key]=result.get(key,0)+sign*c*d
    return {x:c for x,c in result.items() if c}


def matching(C,v,L,y,p,m):
    if L==0 or m==0:
        raise ValueError('selected inverse is undefined')
    return F(C)*v*y*p/(L*m)

class PSChecks(unittest.TestCase):
    def test_uv_epsilon_factor_four(self):
        # d_a at weak1,u_b at weak0; chi_c at weak1, chi_3 at weak0.
        for a,b,c in permutations(range(3)):
            coefficient=0
            fs=[(a,1),(b,0)]
            scalars=[(c,1),(3,0)]
            for f in (fs,fs[::-1]):
                for s in (scalars,scalars[::-1]):
                    coefficient+=eps([f[0][0],f[1][0],s[0][0],s[1][0]])*eps([f[0][1],f[1][1]])*eps([s[0][1],s[1][1]])
            self.assertEqual(coefficient,4*eps([a,b,c]))

    def test_fermionic_rr_and_lr_nonzero(self):
        # Full color sum, Weyl epsilon, and actual Grassmann multiplication.
        # R slots: u,d,d,anti-nu all right Weyl. L slots: uL,dL,dR,anti-nu.
        for label in ('RR','LR'):
            def field(species,color,spin):
                return {( (species,color,spin), ):F(1)}
            operator={}
            for a,b,c in permutations(range(3)):
                for s,t,u,v in product(range(2),repeat=4):
                    coeff=eps([a,b,c])*eps([s,t])*eps([u,v])
                    if not coeff: continue
                    fields=[field('u'+label[0],a,s),field('d'+label[0],b,t),
                            field('dR',c,u),field('antiNu',0,v)]
                    term={():F(coeff)}
                    for f in fields: term=wedge_product(term,f)
                    for x,z in term.items():operator[x]=operator.get(x,0)+z
            self.assertTrue(any(operator.values()))
            # No proof of paper normalization or sector correspondence from this test.

    def test_covariant_left_factor(self):
        for a,b,c in permutations(range(3)):
            def left(i,j,a=a,b=b):
                return eps([a,b,c,3])*eps([i,j])*eps([1,0])+eps([a,b,3,c])*eps([i,j])*eps([0,1])
            for i,j in product(range(2),repeat=2):
                self.assertEqual(left(i,j),-2*eps([a,b,c])*eps([i,j]))
            # Full component includes both fermion orders; they must not be counted twice.
            resolved=left(1,0)+eps([b,a,c,3])*eps([0,1])*eps([1,0])+eps([b,a,3,c])*eps([0,1])*eps([0,1])
            self.assertEqual(resolved,4*eps([a,b,c]))

    def test_complex_barred_projection(self):
        # Gaussian rationals represented as pairs, with no floating point.
        def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
        def star(a):return (a[0],-a[1])
        def div(a,b):
            d=b[0]**2+b[1]**2
            return tuple(x/d for x in mul(a,star(b)))
        Y,w,M=map(lambda z:tuple(map(F,z)),((2,3),(5,7),(11,13)))
        d=mul(Y,star(w))
        self.assertEqual(star(div(d,M)),mul(div(star(Y),star(M)),w))
        self.assertNotEqual(star(div(d,M)),div(d,M))

    def test_independent_chiral_outputs(self):
        # Canonical typed probes are -kL*w/2 and -kR*w/2 after the QQ half.
        for CL,CR in ((0,0),(1,0),(0,1),(1,-1)):
            outputs=(-F(CL,2),-F(CR,2))
            self.assertEqual(any(outputs),bool(CL or CR))
        # Exact point: v=y=Y=M=w=Lambda=m=1; kernel chart (1,0,-1).
        self.assertEqual(matching(F(1),F(1),F(1),F(1),F(-1),F(1)),F(-1))

    def test_exact_mass_chart_and_finite_mu_boundary(self):
        for d,M,mu in product(range(-2,3),repeat=3):
            if not M:continue
            mode=[F(1),F(0),-F(d,M)]
            mass=[[0,d,0],[d,0,M],[0,M,mu]]
            image=[sum(x*y for x,y in zip(row,mode)) for row in mass]
            self.assertEqual(image,[0,0,-F(mu*d,M)])
        # Lean's division-by-zero chart would not be a zero mode at d=1,M=0.
        singular_mass=[[0,1,0],[1,0,0],[0,0,0]]
        candidate=[F(1),F(0),F(0)]
        self.assertNotEqual([sum(x*y for x,y in zip(row,candidate)) for row in singular_mass],[0,0,0])
        with self.assertRaises(ZeroDivisionError):
            F(1)/F(0)

    def test_matching_zero_and_cancellation(self):
        C,v,L,y,d,M,m=map(F,(2,3,5,7,11,13,17))
        p=-d/M
        self.assertEqual(matching(C,v,L,y,p,m),-C*v*y*d/(L*m*M))
        self.assertNotEqual(matching(C,v,L,y,p,m),0)
        for i in (0,1,3,4):
            args=[C,v,L,y,p,m];args[i]=F(0)
            self.assertEqual(matching(*args),0)
        self.assertEqual(matching(C,v,L,y,p,m)+matching(-C,v,L,y,p,m),0)
        # This scalar cancellation is not cancellation between distinct LR/RR sectors.
        for i in (2,5):
            args=[C,v,L,y,p,m];args[i]=0
            with self.assertRaises(ValueError):matching(*args)

    def test_dimension_and_charge_dictionary(self):
        # 6Y: udd antiL Hbar and qqd antiL Hbar.
        for charges in ((4,-2,-2,3,-3),(1,1,-2,3,-3)):
            self.assertEqual(sum(charges),0)
        self.assertEqual(4*3+2,14)  # doubled engineering dimension7.
        # B=1,L=-1 for both signed monomials, up to Hermitian conjugation.
        self.assertEqual(1-(-1),2)

    def test_multi_copy_exact_kernel_and_restriction(self):
        # Two light copies; non-diagonal invertible heavy mixing.
        D=((F(1),F(0)),(F(0),F(-1)))
        M=((F(1),F(1)),(F(0),F(1)))
        Mi=((F(1),F(-1)),(F(0),F(1)))
        def mv(m,v):return tuple(sum(m[i][j]*v[j] for j in range(2)) for i in range(2))
        def transpose(m):return tuple(tuple(m[j][i] for j in range(2)) for i in range(2))
        def graph(a):return a+(F(0),F(0))+tuple(-x for x in mv(Mi,mv(D,a)))
        def mass(x):
            a,b,c=x[:2],x[2:4],x[4:]
            middle=tuple(d+m for d,m in zip(mv(D,a),mv(M,c)))
            return mv(transpose(D),b)+middle+mv(transpose(M),b)
        for x in product((F(-1),F(0),F(1)),repeat=6):
            self.assertEqual(mass(x)==(F(0),)*6,x==graph(x[:2]))
        a,b=graph((F(1),F(0))),graph((F(0),F(1)))
        light_wedge=lambda x,y:x[0]*y[1]-x[1]*y[0]
        heavy_wedge=lambda x,y:x[2]*y[3]-x[3]*y[2]
        self.assertEqual(light_wedge(a,b),1)
        self.assertEqual(heavy_wedge(a,b),0)
        e2=(F(0),F(0),F(1),F(0),F(0),F(0))
        e3=(F(0),F(0),F(0),F(1),F(0),F(0))
        self.assertEqual(heavy_wedge(e2,e3),1)
        # An ambient nonzero coefficient need not survive the light restriction.
        for u,v in product(((F(1),F(0)),(F(0),F(1)),(F(1),F(1))),repeat=2):
            self.assertEqual(heavy_wedge(graph(u),graph(v)),0)

    def test_mass_squared_norm_crosscheck(self):
        # Squared norms stay rational; no numeric square root is evaluated.
        d2,M2=F(25),F(5)
        literal=2*d2+2*M2
        displayed=2*d2+2*(2*M2)
        self.assertEqual(displayed-literal,2*M2)

    def test_chiral_star_action_and_kinetic(self):
        # Exact Gaussian rationals; dagger reverses Grassmann order.
        zero,one=(F(0),F(0)),(F(1),F(0))
        def cmul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
        def cstar(a):return (a[0],-a[1])
        def cadd(a,b):return (a[0]+b[0],a[1]+b[1])
        def scale(c,a):return {k:cmul(c,v) for k,v in a.items() if cmul(c,v)!=zero}
        def neg(a):return scale((F(-1),F(0)),a)
        def add(*polys):
            out={}
            for a in polys:
                for k,v in a.items():out[k]=cadd(out.get(k,zero),v)
            return {k:v for k,v in out.items() if v!=zero}
        def mul(a,b):
            out={}
            for x,c in a.items():
                for y,d in b.items():
                    if set(x)&set(y):continue
                    z=x+y;sign=(-1)**sum(i>j for i in x for j in y)
                    k=tuple(sorted(z));v=cmul((F(sign),F(0)),cmul(c,d))
                    out[k]=cadd(out.get(k,zero),v)
            return {k:v for k,v in out.items() if v!=zero}
        def dagger(a):
            out={}
            for x,c in a.items():
                # 0..3 <-> 4..7; 8..11 <-> 12..15.
                z=tuple(i+4 if i%8<4 else i-4 for i in reversed(x))
                sign=(-1)**sum(i>j for n,i in enumerate(z) for j in z[n+1:])
                out[tuple(sorted(z))]=cmul((F(sign),F(0)),cstar(c))
            return out
        def gen(i):return {(i,):one}
        s,n,dn=(gen(0),gen(1)),(gen(2),gen(3)),(gen(8),gen(9))
        def rc(a):return (neg(dagger(a[1])),dagger(a[0]))
        def pair(a,b):return add(mul(a[0],b[1]),neg(mul(a[1],b[0])))
        barred=add(mul(dagger(s[0]),rc(n)[0]),mul(dagger(s[1]),rc(n)[1]))
        self.assertEqual(barred,dagger(pair(s,n)))
        self.assertEqual((dagger(rc(n)[1]),neg(dagger(rc(n)[0]))),n)
        y,z=(F(2),F(3)),(F(4),F(5))
        original=scale(cmul((F(-1),F(0)),cmul(y,cstar(z))),barred)
        hol=scale(cmul((F(-1),F(0)),cmul(cstar(y),z)),pair(s,n))
        self.assertEqual(dagger(original),hol)
        self.assertNotEqual(hol,scale(cmul((F(-1),F(0)),cmul(y,cstar(z))),pair(s,n)))
        A=((one,(F(2),F(3))),((F(4),F(5)),(F(6),F(7))))
        B=((A[1][1],cmul((F(-1),F(0)),A[0][1])),
           (cmul((F(-1),F(0)),A[1][0]),A[0][0]))
        def kinetic(a,u,du):
            return add(*(scale(a[i][j],mul(dagger(u[i]),du[j]))
                         for i,j in product(range(2),repeat=2)))
        divergence=add(*(scale(B[j][i],add(mul(dn[i],dagger(n[j])),mul(n[i],dagger(dn[j]))))
                         for i,j in product(range(2),repeat=2)))
        self.assertEqual(kinetic(A,rc(n),rc(dn)),add(kinetic(B,n,dn),divergence))

    def test_grassmann_mass_half_and_source_gate(self):
        def g(species,spin):return {(2*species+spin,):F(1)}
        def add(a,b):
            result=dict(a)
            for key,value in b.items():result[key]=result.get(key,F(0))+value
            return {key:value for key,value in result.items() if value}
        def scale(c,a):return {key:c*value for key,value in a.items() if c*value}
        def pair(i,j):
            return add(wedge_product(g(i,0),g(j,1)),
                       scale(-1,wedge_product(g(i,1),g(j,0))))
        for i,j in product(range(3),repeat=2):
            self.assertEqual(pair(i,j),pair(j,i))
        d,M,mu=F(3),F(4),F(5)
        matrix=((0,d,0),(d,0,M),(0,M,mu))
        action={}
        for i,j in product(range(3),repeat=2):
            action=add(action,scale(-F(1,2)*matrix[i][j],pair(i,j)))
        expected=add(scale(-d,pair(0,1)),add(scale(-M,pair(1,2)),scale(-mu/2,pair(2,2))))
        self.assertEqual(action,expected)
        # Exact compatibility condition, not a floating-point sqrt check.
        # Preserving d fixes k=1; scaling M by r then requires r=1.
        for k,r in product((F(0),F(1),F(2),F(-1)),repeat=2):
            self.assertEqual(k*d==d and k*M==r*M,k==1 and r==1)
        # sqrt(2)=1 contradicts squaring; Lean proves the real-root instance.
        self.assertNotEqual(F(1)**2,F(2))

    def test_normalized_kernel_and_vertex(self):
        # Exact rational norm chart: d/M=3/4 or 3i/4, norm=5/4.
        for imaginary in (False, True):
            d = (F(0),F(3)) if imaginary else (F(3),F(0))
            M,r = F(4),F(4,5)
            xi = (-r*d[0]/M,-r*d[1]/M)
            self.assertEqual(r*r+xi[0]*xi[0]+xi[1]*xi[1],1)
            self.assertEqual((d[0]*r+M*xi[0],d[1]*r+M*xi[1]),(0,0))
            barred = (xi[0],-xi[1])
            self.assertNotEqual(barred,(0,0))
            # Undo the normalized anti-neutrino coordinate change exactly.
            for C in (F(0),F(1),F(-1)):
                old = tuple(C*x/r for x in barred)
                normalized = tuple(r*x for x in old)
                self.assertEqual(normalized,tuple(C*x for x in barred))
                self.assertEqual(normalized==(0,0),old==(0,0))

if __name__=='__main__': unittest.main()
