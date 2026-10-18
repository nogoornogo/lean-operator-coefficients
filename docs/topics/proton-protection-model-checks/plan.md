# Staged Verification Plan

## Common Contract

The target is the existing common-copy inlet, not a classification of stable
protons. For a fixed model, first record the actual SM-stage matter space and
residual action. Identify finite-dimensional common copy representations S,T,
source semisimplicity, and the dimension inequality. Check the full-copy
embeddings, dual-field maps and equivariant mass squares required by
[PhysicalCommonCopyModel](../../../Physics/FieldTheory/Mass/PhysicalCommonCopyModel.lean).
A species-specific kernel must be identified inside the radical of the actual
invariant symmetric mass; dimension counting alone is insufficient.

Keep separate: one specified mass admitting a Realization, and a Model admitting
all invariant symmetric masses on a fixed matter/action space. Failure of a
proposed realization is not proof that no realization exists. A necessary
condition failing on the physical light spectrum can establish inapplicability;
an unavailable representation construction is an unresolved obligation.

Before each implementation, freeze:

- The gauge group or covering group, field representations and VEVs, and the
  actual residual H; quotient descent is a separate obligation when needed.
- Right-handed fields versus left-handed conjugates, hypercharge normalization,
  baryon/lepton normalization, and physical qque conventions.
- The unbroken-SM stage used for the mass radical; distinguish it from masses
  after electroweak breaking. Specify allowed mass parameters and any tuning.
- The exact statement, literature inputs, independent sector definition,
  required Lean interfaces, and finite stopping condition.

The comparison concerns an SM-, H- and Lorentz-invariant physical qque exterior
coefficient on specified light ranges. Its nonzero space means that symmetry
allows a coefficient; it does not prove UV matching, a decay amplitude or a rate.
An exact residual-charge obstruction, if proved, is a useful negative control.

## 1. Gauged Baryon And Lepton Numbers

Use Duerr–Fileviez Pérez–Wise v2, the Section IV N=1 model, with the Section III
field assignment. Derive the VEV stabilizer and qque character from normalized
charges; do not assume a Z3 acting on fractional baryon charges. Specify the
global-group convention and separate any quotient issue from a covering-group
calculation. Verify selected light fields and exotic mass kernels where the
chosen statement requires them. Neutral-sector Majorana terms need not be
excluded by assuming a global Dirac normal form.

Endpoint: an exact charge/invariance certificate for the specified residual
model, and an explicit comparison with the common-copy conditions. Identify
whether a light-range representation obstruction or another admission condition
explains inapplicability; do not infer it merely from the paper's stability claim.

## 2. Split-Multiplet SU(5)

Use Fornal–Grinstein v2. Freeze the light assignments from the 5-bar/10 and
40/50 sectors and the scalar content before constructing mass maps. Distinguish
exact zero mixing from a tuned mass determinant and account for electroweak
terms if making an exact physical-light claim. Record the scope of the claimed
lepton parity: some UV couplings break it, and the paper's nonlinear symmetry
breaking prescription is an additional input.

Endpoint: an exact selected light-kernel/action comparison showing whether
common S,T and the required mass squares exist, with tuning and symmetry scope
explicit. If full higher-representation branching needs new foundations, stop
at a bounded feasibility result or use a clearly parameterized SM dictionary;
never label a supplied branching table a Lean-proved SU(5) decomposition.
Quantum all-loop stability is outside this endpoint.

## 3. Pati–Salam

Use Dutka–Gargalionis v2. At the phase gate choose one specific matter/scalar and
breaking case from the paper and pin its equation/page locations. The group name
alone does not fix the model. Separate absence of gauge-mediated proton decay
from higher-dimensional baryon-violating operators. As a control, check the qque
B-L character; neutrality alone neither establishes nor excludes other residual
protection. Compare the actual physical light fields with the common-copy inlet.

Endpoint: a specified-model admission comparison and a bounded algebraic
operator/charge certificate where the existing interfaces suffice. Do not
compute matching coefficients, hadronic matrix elements or lifetimes.

## Gates, Verification And Stops

Finish and record one model before starting the next. A phase finishes with a
proved certificate, a counterexample to a proposed implication, or an explicit
scope-bounded feasibility decision. Stop for user judgment if a new foundational
project, changed matter sector, extra physical assumptions or wider computation
would be required. Trinification, string/orbifold constructions and other models
are outside the active three-model plan.

Proof milestones require focused builds, persisted strict transitive axiom
and import audits, layout checks, and one serialized full build. Documentation
milestones require local-link and whitespace checks. Keep all literature
premises visible and all model findings in their model-study records; update the
coverage ledger only with evidence-backed status. Commit verified checkpoints;
merging into master requires a later explicit instruction.
