# Hypercharge character rigidity formalization

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. Finite-weight and
actual-character interfaces force the standard hypercharge pair from the
specified nonzero-generation SM target.

## 2. Inputs And Conclusion

The source Weyl invariance, faithful evaluation and exact target hypotheses
differ by interface; continuous-unitary sources provide the analytic
realization.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Weyl-invariant fifth moments and faithful Fourier evaluation connect actual
torus traces to the finite-weight rigidity theorem.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

- `GUT.PhysicalWeylMomentBridge` and `PhysicalWeylChargeBridge`
  - prove that a dual chiral difference doubles the fifth moment;
  - recover hypercharge character rigidity from either finite-weight or actual torus-trace dual targets;
  - forget residual charges for hypercharge character rigidity, then transport the same resolved dual
    target through the injective standard-key embedding for standard charge-orbit bridge -> Abelian proton-operator neutrality;
  - include arbitrary torsion charges and do not reconstruct self-dual data;
  - are audited by `AuditPhysicalWeylChargeBridge` with standard axioms.

- `GUT.SignedWeylTransposition`
  - constructs a signed representative in `SU(6)` for every transposition of
    two distinct defining coordinates;
  - proves that conjugation by this representative permutes diagonal entries
    by the stated transposition.
- `GUT.AmbientTorus`
  - realizes the five-dimensional compact torus as actual determinant-one
    diagonal matrices in `SU(6)` and recovers every diagonal point;
  - proves continuity and identifies each integral compact-torus character
    with evaluation of the corresponding normalized ambient Laurent monomial.
- `GUT.OneDimensionalUnitaryCharacter`
  - proves that a one-dimensional complex representation acts by a scalar
    monoid character, which is circle-valued under unitarity and continuous
    under joint continuity;
  - combines this with the compact-torus character lattice to obtain a unique
    integral weight.
- `GUT.ContinuousUnitaryWeightDecomposition`
  - restricts a finite-dimensional jointly continuous unitary `SU(6)`
    representation to the actual compact torus and decomposes it into finitely
    many one-dimensional irreducible blocks;
  - assembles their integral weights into a finite basis and a normalized
    `Finsupp` Laurent polynomial, and proves by trace that it evaluates to the
    actual restricted character;
  - transfers the model along representation equivalences and constructs the
    common faithful Weyl-invariant model of every finite virtual source once
    continuous-unitarizable witnesses are supplied.
- `GUT.PhysicalFifthMomentBridge`
  - pushes the canonical ambient `Finsupp` Laurent character to rational
    physical weights, summing all collisions under restriction;
  - realizes the fifteen left-handed Standard Model weights as an exact
    finite character and proves its fifth moment is `smFifthMoment`, while
    arbitrary gauge-singlet index at zero weight contributes nothing;
  - proves that an exact nonzero-generation SM-only restriction forces the
    standard pair `(m,n)=(-2,3)`, both for an abstract virtual Laurent model
    and directly for finite virtual continuous-unitary physical sources.
- `GUT.PhysicalTorusCharacterBridge`
  - defines the integral four-dimensional physical weight lattice and proves
    that its restriction to rational weights agrees with the hypercharge character rigidity model;
  - embeds the physical compact four-torus into the actual ambient diagonal
    torus for every integral pair `(m,n)` and proves exact compatibility of
    ambient and restricted Fourier monomials;
  - proves the physical Fourier evaluator faithful, so equality of the actual
    restricted character with the explicit SM-plus-singlets character on the
    compact torus yields the exact finite-weight hypothesis and forces
    `(m,n)=(-2,3)` for nonzero generations in the continuous-unitary scope.
- `GUT.PhysicalSMTorusTarget`
  - constructs the actual one-dimensional compact-physical-torus
    representation associated with every integral physical weight and proves
    its trace character is the corresponding Fourier monomial;
  - realizes every finite integral `Finsupp`, including the exact
    SM-plus-singlets target, as an actual finite virtual representation;
  - constructs the physical-torus homomorphism into the determinant-one
    diagonal `SU(6)` torus and proves that character equivalence between the
    restricted source and this target forces `(m,n)=(-2,3)` for nonzero
    generations, including the continuous-unitary source specialization.
- `GUT.ColorNeutralBranch`
  - defines a normalized four-variable `Finsupp` Laurent model for the
    color-neutral diagonal subtorus and proves compatibility of its `(5 6)`
    action with the actual signed Weyl representative;
  - proves Laurent evaluation on the actual compact torus is faithful and
    computes the normalized SM chiral target explicitly;
  - proves every finite virtual `SU(6)` restricted character is fixed by the
    transposition but the target is not, excluding all nonzero generation
    counts even after arbitrary gauge singlets are added.
- `GUT.ColorNeutralSMGroup`
  - constructs the concrete injective block embedding
    `SU(3) x U(2) -> SU(6)` and realizes every color-neutral diagonal torus
    point in its image.
- `GUT.ColorNeutralSMTarget`
  - constructs the five physical SM multiplets as actual finite-dimensional
    representations of `SU(3) x U(2)` and forms their finite virtual chiral
    target;
  - identifies its trace character on the lifted torus with the normalized
    Laurent target and derives the physical no-uplift theorem.
- `GUT.DegreeFiveWeylInvariant`
  - proves a weighted-generator normal form for symmetric homogeneous
    degree-five polynomials in six variables;
  - uses Newton identities to prove that their trace-zero restrictions are
    exactly in the span of `p5` and `p2*p3`.
- `GUT.AmbientWeylMoment`
  - defines a normalized finite `Finsupp` model on rational trace-zero
    ambient weights with the full `S_6` coordinate action;
  - proves that a Weyl-invariant finite virtual weight character has a
    symmetric homogeneous fifth-moment polynomial and applies the preceding
    invariant classification.
- `GUT.FifthMomentHypercharge`
  - embeds every rational physical cocharacter pair `(m,n)` into the six
    trace-zero Cartan coordinates and computes the exact one-generation SM
    fifth weight moment;
  - proves that a full Weyl-invariant ambient fifth-moment source, including
    every nonzero generation multiple, forces `(m,n)=(-2,3)`.

## 6. Scope And Limitations

The result does not reconstruct self-dual matter or classify arbitrary light spectra from an odd moment alone.

## 7. Sources And Verification

The [scope dossier](../HYPERCHARGE_CHARACTER_RIGIDITY.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.
