# Continuous U(1) anomaly cross-check

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Status

`AUXILIARY CROSS-CHECK; LEAN-CHECKED FOR ONE OR FAMILY-UNIVERSAL RATIONAL CHARGE ASSIGNMENT`

## 2. Inputs and conclusion

For a continuous U(1), the proton functionals factor through mixed anomalies:

\[
P_2=A_2-A_3,
\]
\[
P_1=\frac13A_3+\frac12A_2-A_{YYK}.
\]

Hence an exact anomaly-free continuous U(1) cannot forbid those operators.

## 5. Lean entry points

**Lean update:** `GUT/SU6/SelectionRules/StandardBranch/StandardBranchProtonObstruction.lean` defines the
three rational mixed-anomaly coefficients with explicit Standard Model
multiplicities and proves both identities by normalization and ring
calculation.  It then proves simultaneous anomaly cancellation forces both
proton functionals to vanish.  This is a theorem for one charge assignment,
and therefore for family-universal charges.  Cancellation only after summing
family-dependent charges does not imply that each family's proton functional
vanishes; that stronger flavor-dependent statement remains unverified.  This
continuous-U(1) anomaly factorization is logically separate from, and is not
a replacement for, the standard charge-orbit bridge to Abelian proton-operator neutrality Abelian residual-symmetry proof.  In
particular it does not establish the finite Abelian case.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
