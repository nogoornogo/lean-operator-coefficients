# Retired closed numerical example proofs

At the user's explicit direction, the remaining two closed numerical example
modules were removed from future builds after `checkpoint 01`. The files here are
byte-for-byte UTF-8 source snapshots, not Lean modules or theorem inputs.
The [manifest](manifest.json) records original paths, source commit and hashes.

- [Computable character numerical examples](SMComputableCharacterExamples.lean.txt)
- [Sparse/cached numerical examples and exact Q6 consumers](SMNeutralSparseExamples.lean.txt)
- The two old audit snapshots preserve which example declarations they checked.

The active audits still check all retained symbolic algorithm correctness and
conditional-consumer endpoints with the unchanged strict axiom policy. Their
old closed-example entries are archived with the corresponding declarations;
this does not weaken the acceptance policy for retained theorems. The earlier
[Q18 archive](../q18-numerical/README.md) remains unchanged as checkpoint evidence.
No exact example equality is reasserted by the new structural support proofs.

A historical source's old import may point to a retired module: these text
snapshots are evidence, not a promise that their former import graph builds.
Generic computable evaluators remain available; proofs derived structurally
from coefficient-basis isomorphisms are retained. No archived module is a
full-build/cache prerequisite, and no change to Lean/dependency pins is needed.
