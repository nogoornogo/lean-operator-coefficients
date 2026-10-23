# Resumed Lorentz Reduction Checkpoint

This records an intermediate checkpoint. Its pending tasks are now discharged
by the [completed result](results.md); its check counts remain checkpoint evidence.

The [completeness contract](completeness-plan.md) remains active. The
[preceding foundation](foundation-progress.md) supplies full relation
annihilation and whole first-jet source coverage. This checkpoint connects
that source with actual Lorentz invariant tensors; it is not a final
coefficient equivalence.

## Actual-source reduction

[Mixed first tensors](../../../Math/Algebra/MixedFirstJetTensor.lean) retain
the even Leibniz derivative on a noncommutative algebra. The derivative can
mark either odd factor or a specified even factor. The
[C5 tensor input](../../../Physics/FieldTheory/Jets/WeylHiggsFirstTensor.lean)
proves grade membership and covariance under arbitrary actual Lorentz
elements. A linear extension is required to be invariant only on the
selected grade.

[Source coverage](../../../Physics/FieldTheory/Jets/WeylHiggsFirstSource.lean)
proves that these words span the entire actual grade, including all
chirality choices, component labels and derivative allocations. Reordering
the even factors retains the full odd exterior factor.

The [Lorentz controls](../../../Physics/FieldTheory/Jets/WeylDirectionInvariant/Basic.lean)
derive every finite row from four concrete SL(2,C) elements. The generated
LL, LR, RL and RR certificates are rechecked by Lean: same-chirality
spinor/dual-vector coefficients vanish, while each opposite-chirality
coefficient is determined by one component. These are necessary constraints
of actual full-group invariance, not assumptions about Lie algebra rows.
The [inverse-Pauli contraction](../../../Physics/FieldTheory/Jets/WeylDirectionInvariant/Pairing.lean)
is independently proved invariant under arbitrary group elements.

[Weyl upper constraints](../../../Physics/FieldTheory/Jets/WeylHiggsLorentzUpper.lean)
and the [odd swap](../../../Physics/FieldTheory/Jets/WeylHiggsOddUpper.lean)
then prove that both odd derivative allocations vanish for every admitted
invariant functional. The swap explicitly retains the Grassmann minus.

## Lower construction

The [wave sum](../../../Physics/FieldTheory/Jets/WeylHiggsWaveSum.lean) uses
four null directions and exact inverse-Pauli moments. It kills the entire
EOM/IBP relation module and evaluates the candidate to 384i.
The [marked quartic pairing](../../../Math/RepresentationTheory/MarkedFieldPairing.lean)
proves that a field/dual charge insertion commutes with every paired internal
action. These ingredients still need the whole-grade moment formula to
establish invariance of the wave sum itself.

The remaining upper work is the internal Higgs reduction and its IBP row;
the remaining lower work is the arbitrary-group admission of the wave sum.
Normalization, both inverse laws, dimension one and the completed
coefficient-level literature checks depend on those steps.

## Resource repairs

The generated four-chirality build was split into individual builds after
a thread-creation failure. First-jet source identities use separate even-slot
lemmas and explicit tensor congruence. Grading proofs name the algebra,
factor values and degrees to avoid expensive inference. All accepted
proofs retain the original heartbeat/kernel/recursion limits and resource
guards. No failed elaboration attempt is treated as a mathematical result.

## Checked checkpoint

All focused builds and both fresh strict inventories pass. Counts are
31 mixed-tensor, 16 marked-pairing, 163 Weyl/direction, 35 actual-input tensor,
11 source, 18 Lorentz/Weyl-upper and 19 wave-sum declarations: 293 strict
transitive checks, with only the three standard logical axioms allowed.
The public source-coverage theorem transitively audits its private even-slot
helpers as well. Import-layer restrictions are unchanged.

The serialized full `lake build` passes 7982 jobs. Accepted additions have
no tactic/linter warnings. The generator reproduces the checked certificate
sources exactly. The independent finite and native-dictionary diagnostics,
including omission/sign and continue-after-discrepancy controls, still pass;
they retain their diagnostic scope. Layout passes for 2486 modules, and
topic navigation, portable metadata, local links and diff checks pass.
These checks record an intermediate milestone, not the requested endpoint.
