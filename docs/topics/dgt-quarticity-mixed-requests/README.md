# DGT and Quarticity Mixed Request Consumers

- Status: completed; both bounded mixed requests and negative controls verified
- Working branch: proof/dgt-quarticity-mixed-requests
- Integration target: master; separately authorized merge only
- Authorization: user requested DGT and quarticity verification on a new branch.

## Frozen Plan

1. Reuse Request/Satisfies and actual coefficient domains. For DGT construct
   one IR request forbidding absolute B1/B2 at every derivative-free degree
   and allowing each of the two prescribed dipole selector outputs.
2. Prove component extraction. As a negative control, UV selector allowance
   fails for the same specified transitions under Circle; do not mix UV and IR.
3. For quarticity construct one request forbidding all-degree SM/Higgs L2
   and the selected bare nuR exterior-square coefficient, while allowing the
   selected eta-dressed coefficient. Retain separate alphabets and the proved
   common Z4 times Z2 residual action. No full extended alphabet certificate.
4. Prove components and show that additionally forbidding the dressed domain
   is inconsistent with its certified nonzero witness. Reuse admission/action
   bridges; no new carrier foundation or arbitrary extended-L2 classification.
5. Register a strict Physics audit, update source/dossier/assumptions/coverage
   records, run focused/full builds, layout/link/diff checks, and commit.

Stop at these two positive requests and bounded negative controls. No new
paper-wide claim, mass-basis LFV, generated matching, rates, derivatives/EOM/IBP,
UV classification or dependencies. Witnesses may differ by allowed target.
The unrelated docs.zip is preserved. Master integration requires separate direction.

See [results](results.md), [references](references.md), [verification](verification.md).

## Outcome

Both requests are certified using the existing API and model adapters.
DGT IR B1/B2 prohibition coexists with each specified dipole allowance;
UV selector allowance fails. Quarticity SM/Higgs L2 and bare-nuR prohibition
coexist with selected eta-dressed allowance; forbidding that dressed domain
fails. No generic API change or new carrier foundation was needed.
See results for exact domains. The frozen stop condition is reached; the
verified topic was committed on its branch.

## Integration

On stage 01 the user authorized master integration. The bounded child
`proof/non-susy-mixed-candidates` was merged here with `--no-ff` at
`checkpoint 01`; this parent was merged into master with `--no-ff` at `checkpoint 02`.
See [verification](verification.md) for merged-state checks.
