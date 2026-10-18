# Fixed Conventions And Admission

The source is [Dutka–Gargalionis, 2211.02054v2](https://arxiv.org/abs/2211.02054v2),
[versioned PDF](https://arxiv.org/pdf/2211.02054v2), Eqs.(1),(2),(6),(10)–(14),(19)–(24).
Full PS branching is supplied from that dictionary; it is not a new Lean theorem.
The certificate starts with the specified component contractions. The source
paper's higher coefficients C_L,C_R are external inputs.

## Field And Index Dictionary

| Object | Certificate convention |
| --- | --- |
| Color | Fundamental complex 3-vector; epsilon_012=1 |
| Weak | Fundamental complex 2-vector; epsilon_01=1 |
| Weyl | Two-component left/right representations of SL(2,C); independent of weak SU(2) |
| RR pattern | uR,dR,dR,antiL; signed species (1,2,2,8) |
| LR pattern | Q,Q,dR,antiL; signed species (0,0,2,8) |
| Scalar | Hdagger; scalar species 1, a genuine weak dual |
| Integer hypercharge 6Y | RR: (4,-2,-2,3,-3); LR: (1,1,-2,3,-3) |
| B,L | B=1,L=-1 for both patterns; B-L=2; Hermitian conjugates reverse signs |
| Engineering dimension | Four fermions and one scalar: 7; after EW substitution: 6 |
| High-scale VEV | v=〈chi0〉, with vR=sqrt(2)v in the paper's real VEV convention |
| EW VEV | w is the Hdagger component VEV; the unbarred Dirac entry is d=Y*star(w) |
| Colored scalar mass | m=m_chid²; the selected inverse requires m nonzero |
| Heavy neutral mixing | M, separately tracked from the vertex coupling y |
| Neutral mass basis | Holomorphic symmetric three-column chart (nuL,nuR-conjugate,xi), not the paper's mixed four-component notation verbatim |
| Barred projection | p=star(-d/M); using -d/M without conjugation is only correct in a real chart |

The charged Higgs and lepton duals are the repository's actual dual modules,
transported by `weakDualLinearEquiv`; neither is silently replaced by a neutral
weak fundamental. Hypercharges cancel only after all five factors are included.
The neutral Hdagger insertion is `weakDualLinearEquiv (weakBasis 0)`.
The anti-neutrino line is `weakDualLinearEquiv (weakBasis 1)` tensored with a
right Weyl spinor. This latter choice includes the epsilon-induced minus sign
relative to an unsigned first dual component. Keep that sign when comparing
component values; scalar Wilson prefactors and exterior probe values differ.

The source Phi is a bidoublet with two SM Higgs directions. This certificate
selects one effective direction H and its Dirac coupling Y. The reduction of
Eq.(6) to that direction and its quark/neutrino mass relation are supplied
component dictionary inputs, not a proved two-Higgs Phi branching/decoupling
adapter. The result does not quantify over all Phi vacuum configurations.

## Ordering And Statistics

The typed seeds have contractions

- RR: eps3(a,b,c) eps2(l,h) eps2(s,t) eps2(u,z).
- LR: eps3(a,b,c) eps2(x,z) eps2(l,h) eps2(s,t) eps2(u,q).

Their actual-field assembly includes alternating projection and the typed-pattern
stabilizer normalization. RR has two identical dR slots, LR has two identical
Q slots; each stabilizer has size two. An invariant ordered RR seed need not
itself obey identical-field exchange. Projection, rather than an unproved
compatibility assumption, is used. The neutral pure probes evaluate to -1/2
for RR and -1 for LR before the PS-specific LR seed half.

Eq.(19)'s ordered d,u component has epsilon factor 4 from the two fermion and
two scalar orders. Before resolving Q's weak components the LR covariant seed
has factor -2, not -4: its Q,Q weak sum already contains the two fermion orders.
Together with Eq.(20)'s quarter this gives -C_L*v/(2*Lambda) for the covariant
QQ seed. The resolved RR uR,dR seed has -C_R*v/Lambda. Resolving the two Q weak
components recovers the component factor four, proved by a finite Lean identity.
There is no extra second count of those orders.

For scalar elimination the paired variables are independent complexified
coordinates; the selected cross term and its Hermitian conjugate are separated.
No full kinetic propagator, Hermiticity/positivity or scalar-potential theorem
is inferred from this algebraic action. The physical quadratic term is -m; reversing the PS
color order d,u to our u,d order contributes a minus to the current J.
`eliminated_oriented_pair` proves the identity using these two signs explicitly.
The mass-kernel chart has nuL coordinate one and xi coordinate -d/M. It is an
exact, nonzero coordinate on the entire mu=0 kernel; it does not assert unit
kinetic normalization. A nonzero rescaling of this line preserves nonzero,
but its numerical Wilson prefactor changes.

## Normalization Boundary In The Pinned Source

Eq.(2) defines vR=sqrt(2)〈chi0〉, while Eqs.(10),(11) display the vertex coupling
yR with no additional sqrt(2). In a literal component substitution the neutral
mixing coefficient would therefore contain yR*vR/sqrt(2), whereas Eq.(12)
displays yR*vR. The displayed symmetric-matrix expression and its charge-
conjugation/overall mass normalization do not supply a verified conversion
resolving this difference in our dictionary. This is a source-convention
question, not a demonstrated error in the paper.

A bounded cross-check of the cited predecessor
[Dolan–Dutka–Volkas, 2012.05976v2](https://arxiv.org/abs/2012.05976v2),
Eqs.(2.10),(2.15),(2.17), finds vR defined as the component VEV itself and a
corresponding yR*star(vR) mass entry. That older convention does not justify
transferring its formula unchanged to the newer paper's sqrt(2) VEV definition
while retaining the same vertex coupling. No verified conversion was recovered
from this check.

Keep M independent in the general certificate. The real exact control satisfies
M=y*star(v), using the literal component convention, and mu=0. With supplied
barred projection p=-s and v=vR/sqrt(2), `paper_prefactor` reproduces Eq.(24)'s
scalar expression. It does not prove that s is the paper's canonically normalized
mixing angle, or identify that angle with the unnormalized ratio d/M. A complete
numerically normalized Eq.(10)-to-Eq.(24) correspondence is not certified.
