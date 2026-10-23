# Selected Non-SUSY Mixed Requests

[Results and dictionaries](../../../../topics/non-susy-mixed-candidates/results.md)
and [pinned sources](../../../../topics/non-susy-mixed-candidates/references.md)
define two independent bounded consumers of `MixedSelectionRequests.Satisfies`.

- `Physics.DevMohapatraParity.all_bOne_forbidden`: actual derivative-free signed
  SM/Higgs inputs vanish at every fermion/scalar degree for absolute B=1.
  Quark phases are b modulo two, with b=3B; leptons/Higgs are neutral.
- `Physics.DevMohapatraParity.llhh_allowed`: the one-copy Weinberg SM sector is
  nonzero using the proved neutral lepton action.
- `Physics.DevMohapatraSixQuark.selected_nonzero`: a two-flavor u²d²s² evaluation
  is nonzero in the color/Lorentz/statistics/residual coefficient domain.
  Flavor projection transports an existing admissible local coefficient;
  six odd phases cancel. Literal Eq.(4), antisymmetric source coupling and
  full flavored SM-intertwiner transport are outside this certificate.
- `Physics.DevMohapatraSixQuark.satisfies`: packages B1 prohibition and the two
  independent allowances without claiming simultaneous UV generation.
- `Physics.MaZ3Mixed.bare_forbidden`, `dressed_evaluation`, `satisfies`: actual
  SM-singlet right-Weyl and complex chi2 representations with common omega
  phase give zero bare exterior-square domain and a dressed coefficient
  evaluating to one. The Lorentz epsilon form supplies the witness.

The Dev SM/Higgs alphabet excludes odd inert eta; no full-alphabet proton
stability follows. The Ma restriction excludes the full quark/residual-gauge
embedding and other neutrino charges. Neither certificate proves matching,
anomaly cancellation, vacuum selection, mass generation, rates or cosmology.
No literature statement is introduced as a custom axiom.

[Verification](../../../../topics/non-susy-mixed-candidates/verification.md)
records the strict transitive audit and builds. The
[coverage ledger](../../../../verification/proton-protection-model-coverage.md)
records only these selected claims.

## Subsequent Connection

The [Dev connection dossier](DEV_MOHAPATRA_CONNECTION.md) supersedes the
original Dev full-action and selected-contraction gaps above. It certifies
a nonzero physical exterior intertwiner for the source monomial in an explicit
right-Weyl convention, while leaving full normalized UV matching unproved.
