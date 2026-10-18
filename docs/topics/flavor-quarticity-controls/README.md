# Flavor Restriction and Quarticity Adapter Controls

- Status: completed; both scoped coefficient controls proved
- Working branch: `proof/flavor-quarticity-controls`
- Integration target: `proof/koren-sm-selection`, not master
- Parent exception: bounded child of the unmerged Koren topic; child creation
  and integration follow the repository's discretionary child-branch rule.
- Authorization: user requested both candidate verifications, including the
  quarticity adapters subject to implementation burden.

## Frozen Endpoints

1. DGT m=1,n=3 SM/Higgs restriction: construct the actual Circle flavor action
   and its residual Z9 restriction; prove B1/B2 all-degree prohibition on the
   residual SM/Higgs input. On separate actual dipole domains construct
   muon-to-electron/tau selectors, prove UV prohibition and explicit residual
   nonzero coefficients. Prove action restriction/dictionary; do not infer
   generated matching or a mass-basis LFV result.
2. Quarticity Z4 times Z2: construct a neutral-SM-gauge right-handed Weyl
   neutrino adapter (charges 1,1) and an eta scalar adapter (charges 2,0).
   Prove every invariant bare exterior-square coefficient is zero, and
   construct an invariant nonzero exterior-square tensor eta coefficient with
   normalized epsilon evaluation. Connect scalar-free SM/Higgs L2 prohibition
   to the composable interface. Bare versus dressed domains stay explicit.

Adapter burden assessment: existing Weyl right action, epsilon invariant,
exterior universal map, tensor representations and cyclic characters suffice.
No new general representation foundations, derivative/EOM/IBP library,
dependencies, vacuum dynamics or cosmology. One selected neutrino copy is
sufficient for the dressed witness; no complete model alphabet is claimed.
If those existing interfaces fail to suffice, freeze the missing prerequisite
and report its burden before further foundations.

Acceptance: focused builds, persistent strict transitive audits, serialized
full build, layout/link/diff checks, assumption/dossier review and coherent
commits. Stop at these symbolic coefficient results. No master merge or push.

## Pinned Sources

- Davighi, Greljo, Thomsen, *Leptoquarks with Exactly Stable Protons*,
  [2202.05275v2](https://arxiv.org/abs/2202.05275v2),
  [PDF](https://arxiv.org/pdf/2202.05275v2), Secs. II–III, Tables I–II,
  Eqs. (2)–(4), (6), (12)–(15). m=1,n=3 gives quark charge 1,
  electron/tau 0, muon -9, Higgs 0; condensate charges 0,9.
- Centelles Chulia, Ma, Srivastava, Valle, *Dirac Neutrinos and Dark Matter
  Stability from Lepton Quarticity*,
  [1606.04543v1](https://arxiv.org/abs/1606.04543v1),
  [PDF](https://arxiv.org/pdf/1606.04543v1), Sec. II, Table I, Eqs. (1),(11).
  Right-handed neutrino has Z4 charge 1, Z2 odd; eta has charges 2,0.
  A real eta is represented here by its complexified coefficient carrier;
  no real-field functional integral or potential is formalized.

Anomaly freedom, UV generation, condensate existence and paper-wide claims
are not premises established by these coefficient certificates.

## Outcome

Both frozen endpoints are proved, including the selected nuR/eta adapters.
No new foundations or dependencies were needed. See [results](results.md),
[verification](verification.md), the
[proof dossier](../../proof/current/applications/Physics/FLAVOR_QUARTICITY_CONTROLS.md)
and [reader-facing comparison](../../model-studies/flavor-quarticity-controls/results.md).
No remaining work within this bounded endpoint. Integrated into its recorded
parent by `checkpoint 01`, then into master by `checkpoint 02` at stage 01.
