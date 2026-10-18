# DGT and Quarticity Mixed Requests: Results and Boundaries

## DGT: One IR Input

`GUT.DgtQuarticityMixedRequests.dgtDomain` indexes the existing SM/Higgs
B1/B2 union coefficient family over every fermion/scalar degree, and the
actual image of each of the two prescribed IR dipole selectors.
`dgtRequest` forbids the baryon family and allows each selector image.
`dgt_satisfies` proves this one request, reusing `all_bnv_forbidden` and the
certified selected-output witnesses. `dgt_components` extracts every condition.

All components use the existing m=1,n=3 IR Z9 dictionary. The dipole lepton
representation is the restriction of the UV action; its equality to the
appropriate SM flavor action is already proved in the original adapters.
Baryon prohibition covers absolute Delta B=1 and 2 on the derivative-free
SM/Higgs input. Dipole allowance means a nonzero B/W output for each prescribed
mu-to-electron/tau selector in fixed gauge-basis coordinates. It is not a
mass-basis decay, UV generation or all-LFV statement. Witnesses may differ.

`dgt_uv_not_allowed` is a negative control: the corresponding Circle UV
selector ranges are forbidden, so these allowance demands cannot be carried
unchanged from IR to UV. No request combines UV prohibition and IR allowance
as if they described one symmetry action.

## Quarticity: Explicitly Different Coefficient Domains

`quarticityDomain` has three entries sharing the original Z4 times Z2 residual
dictionary but retaining different field domains:

- all-degree SM/Higgs-only absolute Delta L=2 coefficients;
- the selected bare nuR exterior-square invariant coefficient;
- the selected eta-dressed nuR exterior-square coefficient.

`quarticityRequest` forbids the first two and allows the third.
`quarticity_satisfies` reuses the proved actual action/statistics adapters and
the dressed witness; `quarticity_components` extracts the conditions.
`quarticity_dressed_not_forbidden` uses nonzero existence to reject prohibition
of that admitted dressed domain. `quarticity_extended_request_inconsistent`
also checks the generic conflict API for a request that retains dressed
allowance and adds dressed prohibition.

This does not certify all coefficients of the extended field alphabet or
identify dressed allowance with violation of an exact total L assignment for
that entire model. The original SM L2 target and the selected nuR/eta sectors
are explicitly separate. One nuR copy and the complexified real eta with
proved real phases remain the original scope. No vacuum, mass or rate result
is added.

## API Assessment and Endpoint

The existing Request/Satisfies interface needed no foundational or generic API
change. Indexed domains can include all-degree families, fixed-content invariant
spaces and actual selector images. Each permission is checked separately.
The new consumers make the symmetry/domain distinctions explicit and show
why whole-domain allowance or a field-alphabet extension cannot replace the
requested selected-output obligations.

The bounded two-model endpoint is reached with the checks recorded in
[verification](verification.md). This is reuse of existing literature dictionaries,
not new paper-wide verification. Integration of this topic remains separately
authorized.
