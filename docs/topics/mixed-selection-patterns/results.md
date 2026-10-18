# Mixed Request Results and Limits

## Indexed Requests

`Math.MixedSelectionRequests.Request I` specifies two independent subsets of
an index type: forbidden and allowed targets. `Satisfies C r`, for supplied
zero-equipped coefficient domains C(i), means every forbidden domain is zero
and every allowed domain has a nonzero element. `forbidden` and `allowed`
extract component proofs; `combine_iff` combines requests; `conflict` rejects
opposite demands on exactly the same domain; `empty_satisfied` handles no
requests. `transport` reuses certified linear equivalences target by target.

Allowing several targets means a witness for each target. It is stronger than
allowing their union/product, whose nonzero element may occupy just one target.
Witnesses need not be the same coefficient or come from a common interacting
Lagrangian. No degree convention is hidden in Request: the supplied C(i)
fixes it. A fixed-degree domain, an all-degree coefficient family, or an actual
selector range are different inputs and must be labeled accordingly.

## Selected Allowance

`SelectedAllowed s` means that some admitted coefficient has nonzero output
under the prescribed linear selector s. `selected_allowed_iff_range` equates
this to `Allowed s.range`; `range_forbidden_iff` equates range prohibition to
s=0. Thus a selector's image can participate in the same request interface.
`selector_zero_iff_not_allowed` expresses the incompatibility directly.
`whole_domain_not_selected` is a negative control: the whole field-valued coefficient
domain is allowed but its zero selector permits no selected output.

For LFV this is an existence claim about the specified transition/channel,
not merely a nonzero B/W coefficient somewhere else and not all LFV.

## BGW Connection

`GUT.MixedSelectionPatterns.bgwDomain` has three targets. B1 and B2 use products
of the actual one-copy SM/Higgs selected coefficient spaces over all (n,m).
`bgw_domain_forbidden_iff` proves their vanishing equivalent to the existing
all-degree prohibition predicates. LLHH uses exactly
`BgwChargedHiggsWeinberg.Sector`, the charged-Higgs actual domain at (2,2).
Its nonzero witness comes through the previously proved whole-domain
coefficient equivalence, not from neutrality alone.

`bgwRequest` forbids B1/B2 and allows LLHH; `bgw_satisfies` certifies the request
using the prior BGW baryon certificate and actual LLHH witness.
`bgw_components` exposes the three conclusions. The mixed interface introduces
no new model hypothesis, generated coefficient or mass claim.

## DGT Selected-LFV Control

`dgt_selected_allowed` and `dgt_selector_range_allowed` reuse each of the two
actual IR dipole witnesses with nonzero prescribed output. These are IR
allowance controls; the existing UV dipole prohibition remains a different
symmetry input. No simultaneous UV-forbidden/UV-allowed request is asserted.

## Fixed-input q/l continuation

The [fixed-input request facade](../sm-rank-certificates/pattern-input-results.md)
reuses this exact `Request`/`Satisfies` interface for the three-generation signed
SM with a residual-neutral Higgs and cyclic scalar q/l action. Its finite
actual-test domains are proved equivalent at the allowance/prohibition level
to the original all-degree content/Higgs coefficient family. Under the explicit
Weyl reduction input, it replaces supplied carrier/support certificates with
finite charge/multiplicity conditions. The charge-only exclusion route needs
no literature premise. The BGW and DGT examples above keep their distinct
charged-Higgs/selector domains and checked proofs.

## Endpoint

The bounded extension supplies request composition, explicit per-target
permission and existing-model consumers. It does not automatically decide
requests, search UV models, infer admitted nontriviality, or extend local
operator foundations. The twelve-row prohibition catalogue remains intact,
with a linked mixed-request extension rather than a new Cartesian-product
inventory. Verification is recorded in [verification](verification.md).
