# Abelian proton-operator neutrality

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Status

`LEAN-CHECKED ABELIAN CHARGE-GROUP CORE CONDITIONAL ON THE STANDARD CHARGE-ORBIT BRIDGE`

## 2. Inputs and conclusion

The gauge-mediated dimension-6 proton-decay charge functionals

\[
P_1=2k_Q-k_u-k_e,
\]
\[
P_2=k_Q+k_L-k_u-k_d
\]

are therefore neutral under any ordinary residual Abelian symmetry compatible with the SM-only chiral index.

## 5. Lean entry points

**Lean update:** `GUT/SU6/SelectionRules/StandardBranch/StandardBranchProtonObstruction.lean` formulates the
five charges in an arbitrary additive commutative group and proves both
functionals vanish from the explicit equalities
`k_Q=k_u=k_e` and `k_d=k_L`.  `GUT/SU6/SelectionRules/StandardBranch/StandardAbelianCharge.lean` and
`GUT/SU6/SelectionRules/StandardBranch/StandardPhysicalSource.lean` compose this calculation with the standard charge-orbit bridge
charge-profile theorem, both for exact pure-SM profiles and for selected
occupied sectors in family-dependent profiles.  The theorem uses no division
or anomaly assumption and therefore applies in particular to finite Abelian
charge groups.  Applying it to every physical residual symmetry still depends
on the standard charge-orbit bridge source-and-interpretation inputs.  The intended main
standard-branch proof is standard charge-orbit bridge followed by Abelian proton-operator neutrality.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
