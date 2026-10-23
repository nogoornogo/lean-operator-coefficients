# Bounded ScalarBlock Compatibility Stop

## Original Stop Checkpoint

The selected Physlib algebra modules compile as actual dependencies on the
v4.35.0 candidate and pass 12 strict transitive checks. The concrete mass
transports pass 7/10 additional strict checks. Full-project compatibility
fails at `GUT.SU6.Adapters.StandardScalarBlock`; the final full-build inventory
also finds a generation-support recursion limit and a Physlib/TauCeti duplicate
declaration. See [all three failures](dependency-integration.md#initial-stopped-state-inventory).

The original ScalarBlock source is preserved. Its rewrite using
`StandardSMUVMass.mem_radical_iff` does not match the candidate certificate
presentation. A direct mass-form proof of the same original statement was
also tested under the explicit bounds below and did not pass kernel checking.
The failed trial is not retained in the formal source, and no audit is disabled.

The subsequent [repair](compatibility-repair.md) resolves the name collision
and the generation injection itself; the later [projection bridge](carrier-pilot.md)
closes ScalarBlock and passes the whole-project gate. The stopped trial below
retains its original evidence.

## Tested Statement And Candidate

In namespace `GUT.StandardScalarBlock`, with the existing imports and opens,
the following replacement of the original theorem was elaborated and tested:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem embedding_mem_radical (x : Blocks)
    (hc : x.2.2.2.1 = 0) (hw : x.2.2.2.2 = 0) :
    embedding x ∈ (StandardSMUVMass.mass Unit).radical.toSubmodule := by
  rw [InvariantWeylMass.SymmetricMass.mem_radical]
  intro y
  rw [StandardSMUVCoordinates.mass_form_gauge]
  change (StandardSMFullGaugeMass.mass (StandardSMUVFields.neutralCharges Unit)).form
    (StandardSMUVFields.gaugeEquiv (embedding x)) (StandardSMUVFields.gaugeEquiv y) = 0
  have hx : StandardSMUVFields.gaugeEquiv (embedding x) ∈
      (StandardSMFullGaugeMass.mass (StandardSMUVFields.neutralCharges Unit)).radical.toSubmodule := by
    rw [embedding_decomposed, StandardSMFullGaugeMass.mem_radical_iff]
    simp [StandardSMUVFields.reorder, hc, hw, StandardSMUVFields.singletEquiv]
  exact (InvariantWeylMass.SymmetricMass.mem_radical
    (StandardSMFullGaugeMass.mass (StandardSMUVFields.neutralCharges Unit))
    (StandardSMUVFields.gaugeEquiv (embedding x))).mp hx _
```

Reproduction after temporarily applying this candidate:

```sh
LEAN_NUM_THREADS=2 lake build GUT.SU6.Adapters.StandardScalarBlock
```

## Resource Gate And Result

- Local heartbeat bound: 800000, with no recursion-limit increase.
- Operational guards: 16 GiB maximum process RSS and 9 minutes wall time.
- Result: kernel deterministic timeout at the theorem declaration; exit 1.
- Observed elapsed time: 347.9 seconds.
- Observed maximum process RSS: 12917952 KiB, about 12.32 GiB.
- Neither operational guard triggered. Measurements describe this named run,
  not a general solver bound. No passing full-build baseline follows.

Earlier two-million-heartbeat mass trials were stopped after large dependent
expansion. Constructed transport certificates resolved those two model targets
in seconds. They did not resolve this remaining concrete membership conversion.
A local monoid-instance experiment and a concrete certificate packaging
experiment also did not close the gate within default kernel budgets.

## Inspected Boundary And Next Scope

Lean expression inspection distinguishes the group-parent monoid from the
direct product monoid in the inferred and explicitly presented membership
conditions. Both the exact implicit action data and the mass/certificate
projection need a stable consumer boundary. The original statement's type
alone passed an identity check; the unresolved cost lies in its proof conversion.

Further work needs a separately frozen interface for this actual UV source
and its group/monoid presentation, with a bounded consumer and strict audits.
Do not resume by increasing the same resource cap, changing the statement,
disabling the ScalarBlock subtree or weakening an audit. The current result
is a bounded compatibility stop, not derivative/IBP completeness or a successful
whole-project upgrade.

At this checkpoint the candidate child remained unmerged into
`proof/derivative-ibp`; master and remote state were unchanged. These candidate
pins were not an accepted new project baseline until the later compatibility
gate passed.
