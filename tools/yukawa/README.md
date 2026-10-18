# Exact Yukawa Coordinate Calculation

These tools produce **untrusted candidate data**, not Lean theorems. They use
only Python's standard library, integer weights and `fractions.Fraction`.
No floating-point approximation, random sampling, external CAS or new package
is required. See the [topic record](../../docs/topics/yukawa-full-space/README.md).

```sh
python3 tools/yukawa/full_space.py
python3 tools/yukawa/full_space.py --candidate > /tmp/yukawa-full-candidate.json
python3 -m unittest discover -s tools/yukawa -p 'test_*.py'
```

## Model And Conventions

Matter is `wedge^2(C^6) + (C^6)* + (C^6)*`, in ordered basis `e_i wedge e_j`
for i<j, followed by two labelled dual fundamentals. Scalar coordinates are
the 378 monomials `x_i*x_j` for i<=j, representing `Sym^2(V*)`. Generator
`E_ab` acts on the wedge by the Leibniz rule and on each dual fundamental
by negative transpose; the scalar action is the induced dual symmetric square.

Coefficients represent `B(x,x)/2`. Thus a mixed monomial coefficient is the
corresponding off-diagonal symmetric matrix entry, whereas a square coefficient
is half the diagonal entry. The vacuum polynomial is

```
sum(i=0..4) x_(wedge i,5) * x_(dual copy 1,i)
  + x_(dual copy 0,5) * x_(dual copy 1,5).
```

This is motivated by the existing `StandardSMUVStabilizer.mass_formula` and
`StandardSMExterior.pair_color_singlet` / `pair_weak_singlet`. The script
constructs the coordinate data directly; it is NOT an export whose equality
to all analytic Lean definitions has already been kernel-checked.

## Algorithm And Checks

Weight preservation reduces 378^2 entries to 1704 unknowns. Ten simple raising
and lowering operators give 6780 sparse equations `T*X-X*T=0`. Exact Gaussian
elimination gives rank 1682 and a rational basis with 22 elements. Every basis
vector is checked against every input equation and the basis rank is checked.
Tests additionally check all 30 off-diagonal generators and Cartan/bracket
conventions. Character antisymmetrization gives five irreducible multiplicities
1,2,2,2,3 and independently returns 22 via the squared character norm. For
SU(3), a representation coincidence gives 45 instead; a control checks this.

Evaluating all 22 basis elements at the vacuum produces rank 5. The span is
checked equal to five explicitly prescribed mass directions, not just checked
to have the same dimension. These are two common five-channel pairings and
the three entries of a symmetric singlet matrix. Its polynomial normalization
is independently checked by reconstructing each 27-by-27 mass basis matrix.

The optional JSON contains rational basis vectors and echelon rows as triples
`[column, numerator, denominator]`, all coordinate labels, and vacuum images.
It is a candidate for later certificate checking, not a trusted proof object:
row-reduction provenance and the bridge to actual analytic SU(6) intertwiners
still need Lean verification. Generated output is disposable, not tracked.

The spectrum test exhausts ONLY the 243 tuples in `{-1,0,1}^5`. It checks the
rank formula and exhibits all six nullities; it does not prove arbitrary complex
parameters. The generic small-block rank and assembled-kernel formula are
separately proved in Lean in `SmallSymmetricRank` and audited. Subsequent
[spectrum transport](../../docs/topics/yukawa-full-space/spectrum-transport.md)
and [residual decomposition](../../docs/topics/yukawa-full-space/non-singlet-decomposition.md)
now cover all actual Yukawa evaluations at this vacuum. The
[actual coupling-kernel split](../../docs/topics/yukawa-full-space/coupling-kernel.md)
also proves quotient dimension 5, independently of these scripts. Full
coupling dimension 22 and evaluation-kernel dimension 17 remain unverified
external numbers, distinct from the proved mass-image classification.

Source references for character arithmetic are recorded in the topic. No
literature statement or computed value is imported as an axiom or hypothesis.
