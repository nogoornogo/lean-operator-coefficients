# Fifth exterior assembly verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](colored-fifth-assembly-results.md).

The structural numerical import exclusions, strict axiom allowlists,
dependency pins and default Lean limits are unchanged.

Focused checks use the one-thread guard, 6 GiB sampled process-group RSS cap,
4 GiB host reserve and 300-second wall cap:

- `ZeroSummands` and `SU2IsotypicIdentify`: complete equivariant zero-factor
  removal and actual multiplicity identification pass.
- `ColorWeakFifthAssembly`: complete source equivalence passes, 11.8 s,
  peak 5,029,992 KiB; module compile time 9.1 s.
- `SU3DoubleSpinFifth`: passes, 4.8 s, peak 4,947,612 KiB.
- `Physics.StandardModel.Operators.SMQFifthBranching`: both actual-core
  endpoints pass, 5.5 s, peak 5,097,416 KiB.
- Final successful focused logs have zero warnings/errors.

The assembly's dependent inverse uses `Fin.cases` to construct actual data;
finite case reasoning is used only to verify the inverse equations. Keeping
the linear forward map, inverse and their laws in separate declarations
avoids unresolved coercion metavariables in a large equivalence constructor.
An initial manual seventh-degree Physics intertwining proof hit the default
recursion limit; composition through the existing restriction equivalence
passes without a limit change or a statement change.

The four Math modules add 30 strict checks, and Physics adds two endpoint
checks. Math passes all 1207 checks (6.3 s, peak 5,352,440 KiB); Physics
passes all 302 checks (5.3 s, peak 5,476,492 KiB). Guarded default `lake build`
passes all 7229 jobs including Math, Physics and GUT (12.0 s, peak
6,638,480 KiB), with zero warnings/errors and no resource guard triggered.

Layout passes all 1853 modules. Links pass 932 Markdown files, 5745 local
links and 111 fragments, with zero errors. The retirement check passes 19
hashes and confirms 15 retired modules remain absent. New-module proof-token
and limit scans and `git diff --check` are clean. Disposable output remains
under `/tmp`.
