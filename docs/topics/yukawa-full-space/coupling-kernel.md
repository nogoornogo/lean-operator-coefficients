# Coupling Kernel And Evaluation Quotient

Status: completed and verified; parent coupling classification remains open.
Branch `proof/yukawa-full-space`, checkpoint `checkpoint 01`,
integration target `master`; parent coupling completeness remains open.

## Frozen Endpoint

Use the actual full-group intertwiner space already equivalent to all
allowed Yukawas. Construct its linear five-coordinate evaluation map and
a linear section from the five realized couplings. Prove that its kernel
is exactly the couplings vanishing at the specified vacuum, that the
quotient is five-dimensional, and that the full space splits as this
kernel plus five coordinates. Reduce the unproved dimension 22 claim to
dimension 17 of this actual kernel, without assuming either number.
Also construct a nonzero actual coupling in the evaluation kernel as a
control distinguishing coupling classification from mass classification.

No change of matter, scalar, vacuum, bare mass, group, dependencies or
axioms. Do not add a Lie-to-group foundation or accept script ranks as
premises. The complete 22-direction basis remains a distinct open gate.

## Verification

- `lake build Math.LinearAlgebra.Audit.AuditSplitEvaluation
  GUT.SU6.Audit.AuditCouplingEvaluation`: passed, 4259 jobs; 5 generic and
  21 model strict transitive axiom checks. Only propext, Classical.choice
  and Quot.sound. No new-source warnings; existing warnings replayed.
- Full `lake build`: passed, 5879 jobs.
- `python3 -m unittest discover -s tools/yukawa -p 'test_*.py'`: 8 passed,
  1.289 seconds. No script output is used as a theorem premise.
- `node tools/layout/check-layout.mjs`: 828 modules, passed.
- `node tools/docs/check-links.mjs`: 309 files, 1893 local links,
  33 fragments, zero errors. `git diff --check`: passed.
- No web sources consulted. Lean LSP unavailable; used source inspection
  and focused builds. No pins, resource limits or axiom exceptions changed.
  Qque scripts not rerun: their covered definitions are unchanged.

## Result

Let C be the space of actual full-SU(6) intertwiners from the existing scalar
to symmetric forms on the actual matter. `YukawaClassification.equiv` is
the pre-existing bijection between C and ALL allowed Yukawas, not only the
five displayed couplings. Let E be evaluation at the existing specified
vacuum and P the five probe measurements.

The new linear section S is constructed by extending five actual couplings
from the standard basis of complex five-space. The proved identities are:

```
P(E(S(c))) = c
E(f) = massMap(P(E(f)))
ker(P o E) = ker(E)
C ~= ker(E) x complex^5
dim(C / ker(E)) = 5
dim(C) = dim(ker(E)) + 5
dim(C) = 22 iff dim(ker(E)) = 17
```

`unique_decomposition` proves that every actual coupling has a UNIQUE
expression f = k + S(c), with k in ker(E). The equality of evaluated masses
is equivalent to equality of the five coordinates. Existing light-spectrum
theorems therefore depend only on this quotient. This quotient is NOT an
identification of physically redundant interactions: scalar fluctuations
and other scalar inputs can distinguish its representatives.

## Nonzero Kernel Witness

`invisible` is the diagonal pullback of the universal Yukawa by the
equivariant projection onto the exterior-15 matter summand. It is a valid
full-group invariant coupling. Its evaluation at the specified vacuum is
identically zero, but `invisible_probe` evaluates it to 1 at an explicit
scalar and two matter probes. Thus `nonzero_kernel` supplies an actual
nonzero member of ker(E), with no external calculation or dimension claim.
The scalar probe is just a witness of nonzero coupling, NOT a replacement
physical vacuum or a claim about a scalar potential.

## Sources

- [Generic splitting](../../../Math/LinearAlgebra/SplitEvaluation.lean)
- [Actual coupling evaluation](../../../GUT/SU6/Yukawa/CouplingEvaluation.lean)
- [Nonzero invisible coupling](../../../GUT/SU6/Yukawa/InvisibleCoupling.lean)
- [Generic audit](../../../Math/LinearAlgebra/Audit/AuditSplitEvaluation.lean)
- [Model audit](../../../GUT/SU6/Audit/AuditCouplingEvaluation.lean)

The five probe identities are applied through a small generic helper to
avoid kernel unfolding of the entire analytic mass construction. No
heartbeat increase, new axiom or unchecked calculation is used.

## Remaining Gate

No theorem here proves dim(ker(E))=17 or dim(C)=22. The external finite
commutant calculation remains candidate evidence. To close the parent
endpoint one must construct and exhaust the actual invisible directions,
or certify the finite commutant and its relation to the full group action.
The unresolved group-action bridge is not assumed by this milestone.
Keep the parent branch unmerged; do not silently start a new Lie-to-group
foundation. The fixed-vacuum mass and light-spectrum endpoints were already
complete and are not weakened by this remaining coupling-space boundary.
