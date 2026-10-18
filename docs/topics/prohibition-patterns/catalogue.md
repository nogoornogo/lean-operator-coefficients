# Representative Pattern Catalogue

These twelve rows are reusable theorem routes, connections and controls. They
are not twelve UV models or a Cartesian product of targets and assumptions.
All prohibition refers to coefficients; no generated interaction or decay
rate follows. Necessary conditions and iff statements retain their prerequisites.

| ID | Range / input | Output and prerequisites | Checked declaration / connection |
| --- | --- | --- | --- |
| G1 | Any stable selected mixed-field specification | Prohibition iff every selected actual factor vanishes; finite species alphabet, supplied local/residual actions | `Math.ProhibitionInput.factors_iff`, `factor` |
| G2 | Semisimple actual residual sources | Prohibition iff no selected factor shares a constituent with the trivial target; explicit source semisimplicity | `Math.ProhibitionInput.no_shared_iff`, `shared_defeats` |
| G3 | Scalar action on a nontrivial admitted carrier | Invariant-functional prohibition iff some group element detects the scalar; no finite dimension | `Math.ScalarProhibitionNecessity.forbidden_iff_detect`; mixed-factor necessity: `Math.ProhibitionInput.charge_detected` |
| G4 | Standard cyclic scalar character, q in ZMod k | Prohibition iff q != 0, provided Nontrivial carrier and actual scalar action; k > 0 through NeZero | `Math.ProhibitionPatterns.cyclic_forbidden_iff`, `cyclic_neutral_allowed` |
| G5 | Larger-to-smaller symmetry restriction | Forbidden larger source plus allowed smaller target implies non-surjective actual selected map | `Math.ProhibitionInput.restriction_obstruction`; DGT dipole control: `GUT.ProhibitionInputSM.dgt_restriction` |
| T1 | Absolute Delta B=1 on SM/Higgs | Select `BLTarget.bOne`, meaning abs(3B)=3; factor constraints via G1-G3 when their premises hold | `GUT.ProhibitionPatterns.specification`; `koren_chosen`, `bgw_baryon`, `dgt_uv_baryon` provide sufficient examples |
| T2 | Absolute Delta B=2 on SM/Higgs | Select `BLTarget.bTwo`, meaning abs(3B)=6; same routes, separate carrier obligations | Same admitted input and certificates as T1; no universal nonzero-admission theorem |
| T3 | Absolute Delta L=2 on SM/Higgs | Select `BLTarget.lTwo`, meaning abs(L)=2; Koren sufficient prohibition; one-copy LLHH scalar necessity has neutral Higgs | `koren_chosen`; `GUT.ProhibitionInputSM.llhh_forbidden_iff` is bounded to the actual LLHH domain |
| T4 | Prescribed LFV dipole transitions | A selector family vanishes iff each residual selector vanishes; distinct weights give sufficiency, not a general necessary charge test | `GUT.ProhibitionPatterns.joint_iff`; `GUT.ComposableDipoleSelection.forbidden_iff`, `forbidden_of_weights`; `dgt_joint` checks two UV dipole transitions |
| C1 | Any chosen B/L subset, optionally prescribed LFV | Simultaneous prohibition iff all chosen B/L targets are prohibited and all prescribed dipole selectors vanish; no target-combination enumeration | `chosen_iff`, `triple_iff`, `joint_iff` |
| C2 | Empty B/L request | Automatically forbidden; no spectrum/nonzero conclusion | `empty_chosen` |
| C3 | Neutral zero carrier / changed field alphabet | Neutrality does not imply existence on a zero carrier; SM-only prohibition does not extend automatically to added nuR/eta fields | `Math.ScalarProhibitionNecessity.neutral_zero_control`; `GUT.ProhibitionInputSM.quarticity_domains` |

## How to Use the Catalogue

For the **fixed three-generation SM with one residual-neutral Higgs and the
existing cyclic scalar q/l action**, use the
[fixed-input request facade](../sm-rank-certificates/pattern-input-results.md).
Supply k,q,l and forbidden/allowed target sets; the facade constructs the
actual coefficient-test family. `b1ForbiddenB2Allowed` requests B1 prohibition
and B2 allowance. Under the explicit Weyl reduction input, `b1_b2_iff` requires
exclusion of every selected B1 finite entry and one actual B2 entry with neutral
q/l charge and positive local multiplicity. The bridge to original all-degree
spaces is proved; no assumed nontrivial carrier is added. Charge-only exclusion
also has a direct unconditional route. Spectral coefficients are noncomputable,
so this is a proof-input facade rather than an executable request checker.

The G1--G5 routes and existing charged-Higgs/LFV model examples retain their
original domains and hypotheses. Use the following general interface for
other residual actions, flavor carriers or scalar/selector dictionaries.

For B1 plus L2 choose `{t | t = .bOne ∨ t = .lTwo}`; for all three choose
`Set.univ`. `chosen_iff` exposes exactly the requested premises at all degrees.
Changing that set does not change the admitted fields. G1-G5 are reusable
conditions on each applicable input, not six independent knobs to multiply.

`JointForbids` is a conjunction of mixed-field prohibition and a dipole-selector
condition on their respective actual domains. Its parameters permit independent
residual groups; a model application must supply compatible dictionaries.
`dgt_joint` uses the same Circle UV residual group for both. Its UV baryon
prohibition is proved by restriction to the existing protected Z9 input and
preservation of the underlying coefficient linear map. It does not combine
UV LFV prohibition with IR LFV allowance as if they were one symmetry input.

## Connection Gaps and Limits

The [converse inventory](../inverse-cyclic-sm-construction/converse-inventory.md)
separates existing iff criteria from one-way numeric/charge filters and ranks
bounded parameter adapters. It is a source-inspected assessment, not new proof
coverage or a classification of every sufficient condition in this repository.

B1/B2/L2 selection is all-degree and derivative-free, but selection alone
supplies neither a proof of prohibition nor a nonzero quotient carrier.
G3/G4 necessity therefore needs content-specific admitted nontriviality.
The fixed q/l facade handles that fixed-input support through the constructed
actual tests and extraction, without adding G3/G4 nontriviality as a premise.
Koren/BGW examples supply sufficient certificates, not complete model
classifications. No new saturation or arbitrary-sector nonzero theorem is
claimed. LLHH is one complex lepton flavor copy with neutral Higgs flavor;
charged Higgs cases keep their prior separate coefficient bridges.

T4 covers explicitly prescribed B/W dipole transitions. It is neither all LFV
nor a predicate on total lepton number. No new converse asserting that every
LFV prohibition arises from distinct scalar weights is proved. The catalogue
can be extended with other certified selectors without multiplying every
existing B/L target combination into a new proof record.

## Mixed Prohibition and Allowance Extension

The [mixed-request results](../mixed-selection-patterns/results.md) add explicit
per-target allowance to the patterns. Requests separately list forbidden and
allowed domains; combining requests preserves every individual condition.
Allowance of a union does not replace allowance of each requested target.

| Extension | Concrete input and output | Checked connection |
| --- | --- | --- |
| Mixed coefficient request | Every forbidden domain is zero and every allowed domain has a nonzero coefficient; opposite requests on the same domain are inconsistent | `Math.MixedSelectionRequests.Satisfies`, `combine_iff`, `conflict` |
| BGW mixed example | All-degree B1/B2 prohibition plus actual charged-Higgs LLHH allowance at degree (2,2) | `GUT.MixedSelectionPatterns.bgw_satisfies`, `bgw_components` |
| Prescribed LFV allowance | Some coefficient has nonzero prescribed selector output, equivalently the actual selector range is allowed | `selected_allowed_iff_range`; `GUT.MixedSelectionPatterns.dgt_selector_range_allowed` |

Degrees and symmetry dictionaries belong to each supplied domain. These
requests assert coefficient existence, not generation or observable rates.

The [DGT/quarticity mixed consumers](../dgt-quarticity-mixed-requests/results.md)
add two checked applications: DGT IR B1/B2 prohibition plus allowance of each
specified dipole output, and quarticity SM-only L2/bare-nuR prohibition plus
selected eta-dressed allowance. UV selector allowance fails in DGT; extending
quarticity prohibition to the certified dressed domain also fails. These
controls keep symmetry changes and field-domain changes explicit.
