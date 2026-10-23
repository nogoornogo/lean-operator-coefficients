# Master integration

The user explicitly requested integration of the completed C4 topic before
starting C5. The recorded working branch was merged into master with
`git merge --no-ff`, preserving the complete topic history without conflicts.
The integration does not change the proved hypotheses, dependency pins or
published interfaces. No remote update is included.

On the merged state, all four [strict audits](verification.md) were freshly
elaborated, covering 5619 transitive declaration checks with only propext,
Classical.choice and Quot.sound allowed. The serialized bounded `lake build`
passes 7947 jobs. The same two-core/two-thread, 16 GiB, default Lean limits
and 180/540-second focused/full ceilings are retained. Existing module-system
import advisories remain; there are no new proof failures.

Both exact diagnostics were rerun:

```sh
python3 tools/derivative-literature/check-higgs-four.py
python3 tools/derivative-literature/check-higgs-literature.py
```

They pass quotient separation, 15504 divergence checks and the native
Murphy/Li/Eboli comparisons, including the local-discrepancy continuation
control. These diagnostics remain independent checks, not Lean premises.
The reference register and central bibliography already contain the final
three-source roles and need no bibliographic change at integration.

Layout, default topic/outcome navigation, portable metadata, local links and
`git diff --check` pass. The integration documentation is a subsequent
documentation-only change and does not introduce another Lean baseline.

Before local branch retirement, its HEAD was checked reachable from master,
with no worktree using it and no pending child branch needing it. The local
branch was deleted with `git branch -d`; its historical name remains in the
topic record. Unrelated worktrees and branches were preserved.
