# Uniform Protection and Exact Radical

- ID: yukawa-exact-radical
- Status: completed
- Checkpoint detail: completed; integration recorded by Git.
- Working branch: `proof/yukawa-exact-radical`.
- Integration target: `master`.

## Frozen Endpoint

Complete the uniform-protection consumer for actual linear UV families.
For an arbitrary invariant symmetric mass and prescribed subspace L contained
in its radical, construct the form on V/L and prove nondegeneracy iff the
radical equals L. Apply this criterion pointwise and existentially to mass
families, including vacuum-generated families. Equality must remain a tested
condition, not a consequence of inclusion alone. No model decomposition,
finite-dimensionality, physical amplitude or new premise is introduced.

## Results

- [Exact radical and quotient form](../../../Physics/FieldTheory/Mass/ExactRadical.lean)
- [Uniform and generated-family consumers](../../../Physics/FieldTheory/Yukawa/ProtectionKernel.lean)
- [Strict audit](../../../Physics/FieldTheory/Mass/Audit/AuditExactRadical.lean)

`family_protected_iff` closes the missing consumer: when every generated mass
extends B, protection for every linear parameter is equivalent to zero
obstruction map and zero bare offset. This extends the existing equation-level
classification to the actual UV-generated family.

For any symmetric invariant mass m and any subspace L included in its radical,
`quotientForm` descends the mass to both arguments of V/L, using symmetry.
`nondegenerate_iff` proves that this quotient form is nondegenerate iff
`radical(m) = L`. `exact_iff` includes the containment requirement explicitly.
`family_exists_iff` gives the corresponding existence criterion in any mass
family, and `generated_exact_iff` specializes it to the actual linear UV
Yukawa family at the fixed residual-invariant vacuum.

These are necessary and sufficient tests, not an unconditional assertion that
a suitable coupling exists. No automatic nondegeneracy proof or search is
claimed. Inclusion alone can leave additional light fields; equality requires
the quotient test. L is an arbitrary algebraic subspace here; no quotient
representation or residual-action theorem is asserted without stability of L.
The generated masses retain their already proved residual invariance. No
finite-dimensionality or model-specific numerical input is needed.

## Verification

- Focused audit build passed, 3644 jobs and eight strict transitive checks,
  allowing only propext, Classical.choice and Quot.sound.
- Full `lake build` passed, 5885 jobs. Existing dependency warnings replayed;
  no new-source warnings.
- Layout passed: 834 modules. Documentation links and `git diff --check`
  passed. No model scripts rerun because their definitions were unchanged.
- Source reads and Lean CLI used; no Lean LSP was available. No external
  literature, new assumptions, pin changes or heartbeat increases.

Commit and integrate the verified bounded endpoint; retain the branch.
