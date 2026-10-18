# Frozen Plan and Acceptance Gates

## 1. Fixed input class

- Gauge action: the existing standard SM covering group, with direct-product
  cyclic residual action Z_k. This is a chosen extended-SM family, not an
  assertion that a SU(5) or SU(6) UV lift exists.
- Orders: 2 through 12 inclusive. Enumerate all charge tuples within this
  range, including nonfaithful assignments; label the effective action order
  if proved. Do not discard equivalent tuples without a proved equivalence.
- Fields: three copies each of Q, uc, dc, L and ec, with universal species
  charges; one complex Higgs doublet and its conjugate, with Higgs charge zero.
  No right-handed neutrinos, SUSY fields or extra light fermions in phase one.
- Charges refer to left-chiral fermions. Physical qque uses dual uc/ec, so
  its character is 2q_Q-q_uc-q_ec, not the all-left Yukawa sum.
- All renormalizable charged-fermion Yukawa signatures are required to be
  symmetry-allowed: Q uc H, Q dc H-dagger, L ec H-dagger. Thus q_uc=-q_Q,
  q_dc=-q_Q and q_ec=-q_L modulo k. Actual nonzero invariant contractions
  require the corresponding gauge/statistics proof; charge neutrality alone
  is not called a nonzero Yukawa certificate.
- Main protection request: all-degree absolute Delta B=1 on the admitted
  derivative-free SM/Higgs alphabet. Delta B=2, Delta L=2 and LFV are not
  imposed; their status may be recorded without expanding the endpoint.

## 2. Necessary conditions and finite candidates

Derive the Yukawa constraints and pull the qque necessary condition back to
3q_Q+q_L != 0 modulo k, with actual cyclic species actions and field transport.
Exhaustively enumerate the remaining two-charge parameters for each order.
Use kernel-checked finite arithmetic or a lightweight reproducible script
with separately proved soundness; no script output is a theorem premise.

Report the sizes of the initial domain and the filtered domain, counting
labeled tuples explicitly. These are charge assignments, not physical models.
This finite filter is complete for its arithmetic predicate only. It need
not reject every impossible model or certify every surviving assignment.

## 3. Reverse construction of a survivor

Choose a survivor by a documented deterministic rule: smallest cyclic order,
then least charge representatives among candidates for which the all-degree
prohibition certificate can actually be proved. Reconstruct full SM x Z_k
representations on the actual field carriers; prove that forgetting Z_k
recovers three SM generations and the declared Higgs action.

Reuse the existing all-degree charge-selection machinery. One route derives
an integer charge identity using the field-content hypercharge/Yukawa laws;
a second, only if needed, uses the existing content-support interface. Do
not claim all-degree coverage by inspecting only the four dimension-six BNV
families. Do not infer nonzero coefficients from neutral higher-degree contents.
If neither route closes the all-degree certificate without new foundational
work, stop with explicit remaining premises and charge-level results.

## 4. Actual mass realization

Construct a massive vectorlike spectator pair with dual residual characters
and an explicit nondegenerate invariant symmetric evaluation mass. The SM
chiral sector has zero invariant high-scale mass. Prove the radical is exactly
the constructed SM fermion space and transport its actual residual action.
Use existing invariant-mass extension/radical assets; do not supply the
radical equivalence or nondegeneracy as unproved inputs to claim construction.
This spectator extension demonstrates an actual algebraic mass realization,
not a mechanism producing the symmetry or an electroweak vacuum.

The Higgs is a separate bosonic carrier. Its neutral action preserves the
chosen residual group under any supplied Higgs VEV, but neither a potential
nor a dynamically selected VEV is proved. Realistic masses and mixing are
outside this first construction.

## 5. Outcomes and stop conditions

- Success: at least one survivor has actual SM content/actions, the invariant
  spectator mass and exact radical, admitted Yukawa contraction evidence,
  and a full selected-domain all-degree B1 prohibition proof. State precisely
  which structures are constructed. No anomaly-free UV-model claim follows.
- Exclusion: a proved obstruction eliminates the entire declared finite class;
  failure to find a witness or a failed applicability check is not exclusion.
- Partial feasibility stop: arithmetic candidates exist but a named physical
  action, contraction, mass or all-degree bridge remains unproved. Preserve
  the candidates as undetermined and do not rename the task to restart it.

Anomaly freedom is not an assumed certificate. It is explicitly unchecked in
this phase, so success is only an algebraic candidate. An anomaly analysis,
new scalar/VEV mechanism, simple-group lift, alternative embedding or expanded
light alphabet needs a separate scoped plan. RGE, matching, QCD, numerical
rates, derivatives and EOM/IBP are excluded.

## 6. Verification and deliverables

Provide sources by layer, persistent strict transitive axiom audits, an
explicit charge convention dictionary, candidate arithmetic and counts, and
an outcome distinguishing necessity, admission and prohibition. Register all
sources/audits, run focused builds followed by one serialized lake build,
layout checks, documentation-link checks and git diff --check. Keep pins and
audit allowlists unchanged. No sorry, custom axioms or native-oracle premises.
Reader-facing successful construction belongs in docs/model-studies; plans,
failed routes and checks stay in this topic. No master merge or push is implied.
