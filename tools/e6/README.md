# External E6 Candidate Experiment

These tools generate **untrusted candidate data**, not Lean theorems.
They are independent project code, using the pinned TauCeti matrices and
Python's standard-library `Fraction`. No CAS installation is needed.
E6-0c now checks a tracked data snapshot in Lean and proves the generated
matrix Lie dimensions 78/45. See the [formal certificate](../../docs/proof/current/inputs/Math/E6_LIE_CERTIFICATE.md).

From the repository root:

```sh
lake build Math.LieGroups.E6.Audit.AuditMinusculeCompact
lake env lean --run tools/e6/ExportMatrices.lean > .lake/e6-0b-matrices.json
python3 tools/e6/lie_certificate.py .lake/e6-0b-matrices.json --summary
python3 tools/e6/lie_certificate.py .lake/e6-0b-matrices.json > .lake/e6-0b-candidate.json
python3 -m unittest discover -s tools/e6 -p 'test_*.py'
```

Optional Lean-data regeneration and comparison (without overwriting tracked data):

```sh
python3 tools/e6/export_lean_certificate.py .lake/e6-0b-matrices.json > .lake/e6-0c-regenerated.lean
cmp Math/LieGroups/E6/Minuscule/LieCertificateData.lean .lake/e6-0c-regenerated.lean
lake build Math.LieGroups.E6.Audit.AuditMatrixLieAlgebra Math.LieAlgebras.Audit.AuditMatrixLieCertificate
```

The emitter adds integer-scaled dual coordinate functionals and well-founded
bracket ancestry. It emits no proofs. `LieCertificateChecks.lean` verifies the
data against the actual pinned matrices using kernel reduction, then the
generic soundness theorems establish the mathematical result.

The exporter uses weight-coordinate entry formulas with kernel-checked
equalities to the pinned matrices. Direct interpreter evaluation of the
partial-equivalence/reflection implementation timed out during the prototype;
this computational view avoids that path without editing the dependency.
Compiled evaluation is still not a proof of the emitted JSON.

The candidate includes integer matrix entries, bracket provenance, rational
row-elimination witnesses, Cartan eigenlabels, and generator-closure coordinates.
The program reconstructs these identities with exact arithmetic, checks
tracelessness, transpose stability, and D5 grade preservation, and rejects
unexpected ranks. The checks remain **external**, even when all tests pass.
The 72/40 nonzero eigenlabels are not a formal root-system identification.

The `.lake` JSON/log outputs are disposable and reproducible. The source tools
and generated Lean data snapshot are tracked. Python is not invoked by the
normal Lean build and cannot discharge a proof obligation. The next step is
the still-missing Lie-algebra identification, followed by the separate
[compact-group contract](../../docs/proof/current/inputs/GUT/E6_MATRIX_PROTOTYPE.md).
