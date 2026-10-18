# Standard-block C4 candidate: a surviving qque coefficient

## Explicit Candidate And Outcome

The [selected route](block-phase-plan.md) combines a standard-block inner
action with an external action. In the actual `15 + bar6 + bar6` basis choose

```text
g = diag(1,1,1,-1,-1,1) in SU(6)
E = (i on 15, i on first bar6, -i on second bar6)
U = rho(g) E
v = diag(1,1,1,1,1,-5), with neutral external scalar action
```

The finite component calculation gives `U² = -id`, `U⁴ = id` and a nontrivial
inner action on UV off-block generators. It fixes `v` and preserves the
standard color and weak blocks. Thus the candidate genuinely drops strict
commutation with all UV SU(6), while retaining the selected unbroken embedding.

Use unit symmetric mass pairings between `15[a,6]` and `second bar6[a]`
for a=1,...,5, and between the two sixth antifundamental components. Its rank
is exactly 12, and its radical consists precisely of the ten `15[a,b]`
components with a,b<=5 and the first five components of the first bar6.
The scalar phases cancel on every massive pair. The full twelve-generator
complexified standard gauge algebra preserves this mass.

This pairing pattern and light identification follow the existing
[full-gauge mass benchmark](../../../GUT/SU6/SelectionRules/Models/StandardSMUVMass.lean)
and [branching dictionary](../../../GUT/SU6/SelectionRules/Models/StandardSMUVFields.lean).
The script fixes its own unit component normalization; it does not prove
equality of its mass matrix with the transported Lean bilinear form.

| Light species (all left handed) | UV source | Six times Y | U phase |
| --- | --- | --- | --- |
| Q | color/weak pairs in 15 | 1 | -i |
| u^c | color/color pairs in 15 | -4 | i |
| e^c | weak/weak pair in 15 | 6 | i |
| d^c | first bar6 color components | 2 | i |
| L | first bar6 weak components | -3 | -i |

Taking the duals of u^c and e^c gives phase `-i` on u_R and e_R. Consequently
the qque four-field phase is `(-i)^4 = 1`. The residual acts trivially on
Lorentz indices. This conclusion is tested on the
actual one-generation Lorentz/Grassmann contraction reused from the
[qque audit](../../../tools/qque/README.md), rather than only on ordered
internal gauge tensors: all 24 nonzero monomials remain invariant, and its
selected coefficient is exactly 2. The witness has Y=0 and Delta B=1.

**This specified candidate fails to prohibit the qque coefficient.** The
surviving coefficient is an allowed invariant, not a computed UV matching
coefficient. No nonzero generated interaction, proton lifetime or assertion
about all standard-block/external actions follows.

## Verification And Boundaries

The [standard-library script](../../../tools/su6-twisted-protection/audit_block_phase.py)
uses exact integer/fraction/fourth-root arithmetic. It exhaustively checks
covariance on all 36 matrix units, mass invariance on twelve standard gauge
Lie generators, the exact 27-by-27 rank and all nonzero qque terms. Negative
controls catch a changed heavy-copy phase and a changed electron phase.
These are reproducible computational checks, not new Lean theorems or a
formal full-group certificate. The residual action is the finite C4 action
defined by the explicit order-four generator; the generator is unitary in
the standard orthonormal component basis.

The UV scalar origin of the mass and quantum exactness of C4 remain
unverified. They cannot repair the already observed failure to forbid qque
for this chosen action and light dictionary. This endpoint does not require
them to reject the proposed symmetry prohibition mechanism.

Verification:

- `python3 tools/su6-twisted-protection/audit_block_phase.py`: six tests passed.
- `python3 tools/qque/audit_one_generation.py`: four tests passed.
- Local documentation links and `git diff --check`: passed.
- No Lean source changed; no Lean build or transitive axiom audit was rerun.
  Earlier Lean checkpoints retain their original scope.

The topic remains open: no protecting solution is constructed. The next
candidate would need a different external action/light placement or relevant
coefficient action; this calculation does not eliminate that broader route.
