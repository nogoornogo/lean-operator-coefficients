# Dimension-Seven Charged Gauge Transports

## Statement And Inputs

`BnvSevenGaugeTransport` gives explicit representation equivalences for the
four positive-baryon typed gauge patterns, including the charged Higgs factor.
All hypercharges remain in the input. Tensor charges are added before removing
their zero total; charged factors are not individually replaced by neutral ones.

The `udd anti-L H*`, `ddd anti-L H` and `qdd anti-E H*` gauge invariant spaces
are transported to the three-color/two-weak core. `udd_unique`, `ddd_unique`
and `qdd_unique` reconstruct every invariant from one transported probe.
`qqd anti-L H*` is transported to the three-color/four-weak core;
`qqd_reconstruction` reconstructs every invariant from two probes.

## Construction

`HyperchargeTensorTransport` proves charge addition, charged-line duality and
balanced four/five-factor transport. The weak dualities are the existing
epsilon-induced equivariant equivalences. Explicit tensor associators and
commutors regroup the neutral tensors. Projection from the actual SM gauge
group onto `SU(3) × SU(2)` is surjective, so invariant transport is two-sided,
not just restriction along a subgroup.

`FourTensorLinearSlot.equiv` gives a generic two-sided equivalence between
four heterogeneous multilinear slots with one linear slot and invariant
functionals on their fivefold tensor product. The linear slot's representation
is arbitrary; in particular, no trivial Higgs action is assumed. Pure-input
evaluation and both inverse identities are proved.

## Boundary

These results classify the gauge factors, not the entire physical families.
Weyl and residual-flavor regrouping, identical-field exchange descent and the
negative-baryon transports remain needed for the dimension-seven endpoint.
No new literature spanning assumption or flavor finite-dimensionality is used.
The dimension-eleven endpoint is still pending.

## Verification

The focused gauge module build passed (3,269 jobs). The charged-line definition
is explicitly noncomputable to avoid a Lean executable-code compiler panic;
the subsequent focused build has no panic. Strict transitive audits and the
full-build baseline pass: 134 checks, 6,469 jobs. Layout checks pass for 1,142
modules; local links and `git diff --check` also pass.
