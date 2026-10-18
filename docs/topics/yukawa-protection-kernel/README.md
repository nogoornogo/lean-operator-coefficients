# Linear Yukawa Protection Classification

- ID: yukawa-protection-kernel
- Status: completed
- Checkpoint detail: completed; integration recorded by Git.
- Working branch: `proof/yukawa-protection-kernel`.
- Integration target: `master`.

## Frozen Endpoint

Parameterize an actual UV-invariant Yukawa family by a complex linear map
into the existing intertwiner space. At a fixed residual-invariant vacuum,
restrict its cross mass to a prescribed radical and construct a linear
obstruction map. Assuming each generated mass extends the original mass,
prove protection iff the obstruction cancels the fixed bare cross term.
For zero bare obstruction classify by the kernel; otherwise prove the
solution fiber is a translate of that kernel, and characterize existence
by range membership. No surjectivity onto all invariant masses, model
decomposition, vacuum minimization or additional physical premise.

Reuse [vacuum protection](../yukawa-vacuum-protection/README.md) and
[Yukawa classification](../../../Physics/FieldTheory/Yukawa/YukawaClassification.lean).
Stop after these general algebraic results and strict audits pass.

## Result

[ProtectionKernel](../../../Physics/FieldTheory/Yukawa/ProtectionKernel.lean)
constructs `family` from a linear map J into actual UV intertwiners, using
the existing exact Yukawa parameterization. At the specified vacuum its
`obstruction` is a linear map from parameters to bilinear cross terms on
the old radical and the added fields. `offset` is the fixed bare cross term.
Neither the obstruction's linearity nor UV invariance is assumed separately.

Writing T for this map and b for the offset, the proved classification is:

```text
protected(p) iff T(p) = -b          (when the mass extends B)
b = 0 => protected(p) iff p in ker T
T(p0) = -b => T(p) = -b iff p - p0 in ker T
exists p with T(p) = -b iff -b in range T
forall p, T(p) = -b iff T = 0 and b = 0
```

`protected_fiber_iff` applies the translated-kernel statement to the actual
generated masses, assuming all family members extend B and p0 is protected.
The set can be empty; no protected base point is silently supplied. Bare and
Yukawa mixing can cancel, so a nonzero bare offset is not replaced by a
homogeneous kernel condition. The statement about all parameters uses that
the entire linear space, including zero, is allowed. A restricted physical
parameter domain would require its own quantification.

No finite-dimensionality, semisimplicity or concrete group decomposition is
required. The target uses ordinary linear maps on the radical; this milestone
does not bundle them as residual intertwiners. The classification preserves
the prescribed included radical, not a potentially rotated replacement light
space, and does not prove exhaustion of the enlarged light spectrum.

## Verification

- Focused `lake build Physics.FieldTheory.Yukawa.Audit.AuditProtectionKernel`:
  passed, 3643 jobs; nine strict transitive axiom checks permitting only
  propext, Classical.choice and Quot.sound.
- Full `lake build`: passed, 5883 jobs. Existing dependency warnings replayed;
  no new-source warnings.
- Layout: 832 modules, passed. Links: 313 files, 1909 local links,
  33 fragments, zero errors. `git diff --check`: passed.
- No external sources, new assumptions, dependency changes or resource-limit
  changes. Model scripts were not rerun: their definitions are unchanged.
  Lean LSP was unavailable; source inspection and CLI builds supplied checks.

Commit and integrate the verified endpoint into master, retaining the branch.
