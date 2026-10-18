# Middle-color product verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](colored-middle-products-results.md).

The five modules add 61 strict transitive checks. The existing allowlist,
structural numerical-import exclusions, Lean/dependency pins and default
proof limits are unchanged. No numerical certificate is introduced.

Focused checks use the one-thread guarded runner, 6 GiB sampled process-group
RSS cap, 4 GiB host reserve and 300-second wall cap.

- `SymmetricCubeContraction` in LinearAlgebra: canonical section and
  contraction identity pass; subsequent rebuild includes nonzero witnesses.
- The representation-level cubic contraction: complete equivariant split
  passes, 6.3 s at peak 4,613,716 KiB before the witness extension.
- The linear partial trace: canonical insertion/correction identities and
  kernel split pass; subsequent rebuild includes nonzero witnesses.
- The representation-level partial trace: complete equivariant split passes.
- `SU3MiddleColor`: final nonzero witnesses and both adjoint-product
  cancellations pass, 9.3 s at peak 4,921,224 KiB. Module compile time 6.5 s.
- The preceding dependency rebuild of all five modules passes in 25.3 s
  at peak 4,909,636 KiB. Final successful logs have zero warnings/errors.

The Math structural audit passes all 1108 strict checks (5.8 s, peak
5,344,992 KiB); Physics retains its 300 checks. The default guarded
`lake build` passes all 7218 jobs including GUT (9.0 s, peak 6,632,940 KiB),
with zero warnings/errors and no resource guard triggered.

Layout passes all 1842 modules. Links pass 926 Markdown files, 5723 local
links and 111 fragments, with zero errors. The retirement check passes 19
hashes and confirms 15 retired modules remain absent. New-module prohibited
proof-token/limit scan and `git diff --check` are clean. Disposable output
remains under `/tmp`.
