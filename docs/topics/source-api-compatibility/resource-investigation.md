# Why The Fierz Resource Failure Appeared During Migration

A controlled rebuild reproduces `std::bad_alloc` with both the original source
and the renamed source before the proof repair. The namespace change is not a
necessary condition for this failure. The checked-in coordinate-based repair
and its passing strict audit are unchanged by this investigation.

## Controlled Comparison

| Source variant | Fresh local dependencies | Unrepaired target | Sampled peak virtual / resident memory |
| --- | --- | --- | --- |
| Original pre-migration source and imports | 11 pass | Allocation failure, SIGABRT | 15.98 / 10.77 GiB |
| Renamed source and imports, original proof body | 11 pass | Allocation failure, SIGABRT | 15.98 / 10.68 GiB |

The [bounded measurement summary](resource-comparison.json) retains the exact
observations. These are per-process samples, not a claim of physical RAM usage
above 16 GiB. Each process had a 16 GiB virtual address-space limit, the same
540-second timeout and `-j2`. Task-manager concurrency does not imply only two
operating-system threads.

The test reconstructed the original module and its entire local dependency
closure in a temporary source tree. All twelve original source checksums match
the [frozen registry](layout-plan.json). Every local dependency was compiled
from source into that tree's own output directory. External dependency artifacts
and the pinned Lean executable were shared; the current repository's compiled
project artifacts were removed from the import search path.

The second tree used the canonical dependency sources. Its unrepaired target
was reconstructed from the original target by changing only import paths and
its namespace; its proof body is identical. It does not import the later
coordinate-based proof repair or legacy compatibility facades. Both trees
compiled modules in dependency order, one compiler process at a time.

For each source, the compiler invocation had the following form, inside the
recorded address-space guard. Variables denote that case's temporary paths and
the dependency-only search path:

```sh
ulimit -v 16777216
LEAN_PATH="$case_build:$dependency_paths" timeout 540 "$lean_bin" -j2 -R "$case_sources" "$case_source" -o "$case_olean" -i "$case_ilean" -c "$case_c"
```

## Why Earlier Build Success Did Not Expose It

The retained pre-migration baseline and pilot build logs replay the existing
contraction-relation audit (`Replayed ...AuditDeltaBTwoContractionRelations`).
They contain no fresh build of the original contraction-relation module.
That success validates an incremental build; it does not establish that this
source proof was regenerated within the same resource guard on those runs.

Relocation and renaming required a new module artifact, which triggered actual
proof regeneration. This explains the difference between the directly observed
pre-migration cached success and post-migration allocation failure. The fresh
original-source control shows that the same limit also rejects the old module.
The earlier explanation had not separated cached reuse from source regeneration.

This does not establish that every historical successful build used caches.
The execution conditions of the original successful proof compilation, including
its address-space limit, are not established by these retained logs. The exact
allocation request and internal proof-processing stage causing the failure were
not profiled. These results therefore do not prove a rename-induced performance
regression or identify all allocator internals.

This follow-up changes documentation and measurement evidence only. It ran the
isolated Lean rebuilds above; the repository-wide `lake build` was not rerun.
The final build and proof-repair acceptance remain those in the
[verification record](verification.md).
