# Actual SU(6) Mass-Index Connection Plan

Status: completed; see [results](physical-index-results.md). Working branch: proof/su6-light-placement-search.
Checkpoint: checkpoint 01; integration target: master, not authorized.

## Frozen endpoint

Connect the five normalized Z5 light targets to an actual finite-dimensional
unitary SU(6) times commuting residual-group representation and an invariant
complex-bilinear symmetric mass on its standard physical restriction.
Use the existing physical-cover descent and standard SU(5) chain to derive
Q/U/E charge-profile equality from the actual radical dual index. Reject
all five targets through faithful cyclic characters. An arbitrary positive
common generation multiplicity and arbitrary singlet index are allowed.

This route avoids individual irreducible branching equivalences for
20,21,35,70: the ambient conjugation argument applies to every actual
representation in this class. It does not certify the supplied finite
branch lists, and it does not identify a general noncommuting residual action
with a product action. The standard embedding and actual radical target
remain explicit physical hypotheses. No assumption of profile equality or
mass invariance under the ambient SU(6) group may be added.

## Routes and stopping conditions

1. Reuse PhysicalChainSource.hasTarget and TorusMassSource.profiles_compatible,
   prove singleton-profile charge recovery, and connect the search formula.
2. Build faithful Z5 circle-valued characters and reject the five normalized
   charges under the actual mass hypotheses.

Stop after the audited physical target obstruction and documentation, or
record a concrete missing prerequisite if these two routes fail. Do not
start a new classification of continuous branching irreducibles.
Verification: focused builds, strict transitive axiom audit, full lake build,
layout, local links, diff and assumption review. No merge or push.
