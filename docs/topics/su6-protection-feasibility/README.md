# SU(6) Protection Model Feasibility

- ID: `su6-protection-feasibility`
- Status: completed
- Result type: structural admission test and algebraic boundary protection
- Working branch: `proof/su6-protection-feasibility`
- Integration target: `docs/publish-v1-upgrade`
- Authorization: user-requested renewed SU(6) protection assessment and explicit
  approval to branch from the current work
- Parent exception: bounded child of the documentation/refactor chain;
  later chain integration into master was explicitly authorized; publication is separate

## Current Boundary-Model Phase

The [boundary model result](../../model-studies/su6-protection/boundary-model.md)
constructs actual exterior-carrier chiral amplitudes, the baryon action,
internal boundary contractions and the SM/Higgs B1 coefficient connection.
The [contract](boundary-plan.md) and [verification](boundary-verification.md)
record the endpoint. Analytic mixed-mode admission and quantum protection
remain explicit boundaries. The earlier standard-class obstruction below
remains valid for its separate mass-radical mechanism.

## Standard-Class Endpoint And Scope

Test whether an existing concrete protecting SM input can be lifted to the
admitted SU(6) class, and identify precisely what a candidate must change if
that lift is obstructed. Start with the constructed three-generation Z2
lepton-parity input, including its actual light mass radical and nonzero
Yukawa coefficients, rather than a new unexplained charge table.

The frozen first route uses the standard embedding, an arbitrary actual
finite-dimensional unitary SU(6) times commuting cyclic-group representation,
an arbitrary invariant symmetric restricted mass, and a positive pure SM
chiral-index target with arbitrary singlet index. The infrared charges are
generation-universal with neutral Higgs and neutral ordinary Yukawa channels.
No ultraviolet representation/copy cutoff is imposed.

The second route reviews the existing SM-preserving unequal-S3 examples and
one published SU(6) boundary-construction example, to distinguish the
finite-mass and boundary-amplitude mechanisms.
No general outer-action, embedding, extra-dimensional or anomaly foundation
will be started. Absence from an old theorem's hypotheses is not evidence
that a protecting model exists.

## Plan And Acceptance

1. Prove a structural admission filter for arbitrary cyclic order: the actual
   SU(6) radical-index condition forces `3q+l=0` for the neutral-Higgs Yukawa
   dictionary. Check the same index filter with a charged Higgs, without
   asserting a new charged-Higgs coefficient classification. Connect the
   neutral-Higgs specialization to the existing actual bounded B1 coefficient iff.
2. Test the Z2 lepton-parity construction on the same dictionary. Retain its
   SM mass/Yukawa/all-degree derivative-free certificate and prove failure of
   its proposed SU(6) lift. Include an allowed-input control and the existing
   S3 realization/full-rank obstructions; no numerical search is a proof.
3. Inspect the source and conditions of the published comparison. Record its
   applicability separately from Lean-certified model admission. Continue to
   the next check after a failed candidate; no paper premise is imported.
4. Run focused builds, persistent strict transitive axiom audits, full
   `lake build`, layout, local-link, topic, metadata and whitespace checks.
   Record the model conditions and scope in the application guide/ledger.
5. Commit the result. Success is either a fully admitted protecting candidate
   or a proved obstruction for the frozen class plus an explicit construction
   boundary. Do not present an infrared example as an SU(6) realization.

## Resources And Stop

Use the existing two-thread convention, 16 GiB address-space cap and
540-second command limit, without higher proof limits, dependency changes,
custom axioms, `sorry` or audit exceptions. If a candidate requires a different
embedding, noncommuting/outer action, non-pure light spectrum or boundary
zero-mode mechanism, state the missing interface and stop before that new
foundation. No matching, rates, RGE, numerical simulation or quantum-exactness
claim is included.

The UV index obstruction is a preliminary model-admission test. New EOM/IBP
interfaces do not supply its missing UV realization. Neither the earlier
derivative-free witness nor a free-input classification is silently asserted
to descend through arbitrary interacting EOM.

## Completed Standard-Class Result

The [reader-facing conditions and checks](../../model-studies/su6-protection/feasibility.md)
state a proved failure of the concrete lepton-parity UV lift and the generic
cyclic admission constraint. The proof allows arbitrary positive cyclic order,
UV representations/copies, positive generation multiplicity and invariant
restricted masses. Higgs charge alone does not remove the index gate; the
coefficient comparison remains on the certified neutral-Higgs domain.

The neutral allowed-input and S3 controls pass. The boundary-based
construction is handled in the separate algebraic phase above. See
[sources](references.md) and [verification](verification.md).
The full build, strict audits and repository gates pass under unchanged limits.

Within the standard finite-mass class the protecting target is excluded,
while the remaining realization interfaces are explicitly identified.
This remains a settled bounded feasibility result, not a general SU(6) no-go
or a construction of a protecting model in that class. Boundary-mode work is
now explicitly authorized in the phase above; unrelated embeddings/actions
are not reopened. The topic is integrated into its recorded parent and later
through the complete chain into master; remote publication has not been performed.

## Parent Integration

Both completed phases are integrated into `docs/publish-v1-upgrade` by an
explicitly authorized `--no-ff` merge. The [merged-state verification](integration-verification.md)
records the full build, direct strict audits, source comparison and repository
checks. The later authorized
[master integration](../source-api-compatibility/master-integration.md)
includes the parent chain and records separate merged-state checks.
The separate input-connection generalization is not part of this result.

## References

- [Existing SU(6) study](../../model-studies/su6-protection/README.md).
- [Actual index obstruction](../../../GUT/SU6/SelectionRules/Models/PhysicalIndexObstruction.lean).
- [Constructed protecting SM input](../../model-studies/inverse-cyclic-sm/README.md).
- [Existing unequal-S3 tests](../sm-support-and-lfv-decomposition/sm-preserving-sample-results.md).
- [Structural proof policy](../../architecture/PROOF_ENGINEERING.md).
