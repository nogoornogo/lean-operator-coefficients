# Conditional Proton-Protection Model Controls

## Statements And Inputs

[ModelControls](../../../../../GUT/Common/ProtonProtection/ModelControls.lean)
uses existing cyclic-charge and physical four-family/exterior sector interfaces.
The dictionaries are explicit supplied broken-phase data, not derived UV models.

- `baryon_selection`: charges (2,2,2,0,0) on Z18 forbid the one-generation
  derivative-free dimension-six four-family BNV sector.
- `baryon_qque_all_flavors`: the same uniform baryon assignment forbids physical
  qque for arbitrary finite Q/u/e flavor index sets, including unequal sizes.
- `light_parity_selection`: charges (0,0,0,1,1) on Z2 forbid the same
  one-generation four-family sector, conditional on this being an exact action.
- `gauge_only_qque_allowed`: the trivial residual one-generation dictionary
  admits a nonzero physical qque family coefficient.
- `equal_scalars_of_common_embeddings`: two injective linear embeddings of a
  common nontrivial source intertwining one source operator with scalar actions
  force the two scalars to be equal. It does not assume a scalar source action.

## Proof And Semantic Boundary

The first certificates instantiate existing cyclic selection equivalences,
which retain SM, Lorentz and exterior-statistics constraints. The all-flavor
qque proof uses its independent symmetric-charge coordinate equivalence and
constant charge6 mod18. The embedding lemma follows from injectivity and
faithful scalar multiplication on a nonzero vector.

[Model studies](../../../../model-studies/README.md) supply source versions,
right-handed/all-left conventions and the model-specific feasibility decisions.
No UV branching, VEV stabilizer, full mass classification or generated matching
coefficient is proved by these declarations. The light-parity dictionary cannot
be inferred to be a symmetry of the full split-model mass. Permission is not
a decay claim; these results do not prove all-operator proton stability.

See the [strict audit](../../../../../GUT/Common/ProtonProtection/Audit/AuditModelControls.lean),
[topic verification](../../../../topics/proton-protection-model-checks/verification.md),
and [literature coverage](../../../../verification/proton-protection-model-coverage.md).
