# E6 Matrix Commutant and Lie Normalizer

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

**E6-0f is complete as an algebraic normalizer theorem.** It uses the actual
minuscule matrices and the checked [real forms](E6_COMPACT_REAL_FORM.md).
No compact group identification, integration theorem, new physical
assumption, or new selection-rule endpoint is asserted.

## 4. Proof structure

### Actual Scalar Commutant

[MatrixCommutant](../../../../../Math/LieGroups/E6/Minuscule/MatrixCommutant.lean) proves that
any complex 27-by-27 matrix commuting with all twelve pinned simple-root
matrices `E_i, F_i` equals `M(0,0) * I`.

The proof does not assume irreducibility:

1. The existing Serre relation gives `H_i = [E_i,F_i]`, so such a matrix
   commutes with all Cartan matrices.
2. The pinned 27 weights are distinct. Comparing entries of `M H_i = H_i M`
   shows that each off-diagonal entry of `M` is zero.
3. `raising_predecessor` is a kernel-checked finite statement: for every
   noninitial coordinate `a`, some raising matrix has entry 1 from `a` to
   a strictly earlier coordinate `b`.
4. Commutation along that edge equates the two diagonal entries. Well-founded
   induction equates every diagonal entry with the entry at coordinate 0.

This proves `commutant_scalar_of_generators` and the exact equivalence
`matrixLieAlgebra_commutant_iff` for the full generated matrix Lie algebra.
The finite check covers all 27 coordinates, not sampled matrices. It uses
kernel reduction, not `native_decide`, an external solver or Python output.

### Exact Normalizer Bound

The reusable
[MatrixLieNormalizer](../../../../../Math/LieGroups/Matrix/MatrixLieNormalizer.lean)
uses mathlib's `LieDerivation.IsKilling.exists_eq_ad`:

- a normalizing matrix `A` induces the actual derivation `x -> [A,x]` on `L`;
- if `L` is Killing, this derivation is `ad(z)` for some `z` in `L`;
- `A-z` commutes with `L`, so a scalar-commutant hypothesis gives
  `A = z + c I`;
- if `L` is traceless and the nonempty matrix size is nonzero in the field,
  `trace A = 0` forces `c = 0`.

The last step is stated over characteristic-zero fields. These are explicit
hypotheses of the **generic** theorem. In
[MatrixNormalizer](../../../../../Math/LieGroups/E6/Minuscule/MatrixNormalizer.lean), all are
discharged for E6: the actual Geck equivalence transfers the nondegenerate
Killing form, and the commutant/tracelessness results come from the matrices.
No extra certificate is supplied to the concrete theorem.

Writing `L` for the complex E6 matrix Lie algebra and `k` for its actual
skew-Hermitian real form, the checked results are:

```text
A in L  <->  A in LieNormalizer(L) and trace(A) = 0

A in k  <->  A in LieNormalizer(k) and A^H = -A and trace(A) = 0
```

The second statement uses real/imaginary decomposition in the already
proved complexification: normalizing `k` implies normalizing `L`.
`compactMatrixLieAlgebra` is the ambient-matrix image of the earlier real
form, with an actual Lie equivalence `compactMatrixEquiv` and real dimension
78. It is not a new, assumed carrier.

## 6. Scope and limitations

### Boundary and Next Checkpoint

These are **Lie-algebra normalizers**, not group normalizers or tangent
spaces of a constructed compact group. The bound is useful for ruling out
extra infinitesimal directions in a later matrix-group construction, but
only after the analytic comparison is proved.

The follow-up **[E6-0g](E6_COMPACT_NORMALIZER.md)** now constructs that
closed compact subgroup of SU(27) and proves the exact all-real-time
exponential criterion. It uses TauCeti's commutator-operator exponential
identity and differentiation at zero; it is not an application of the
abstract manifold tangent or unit-Lie-algebra adapters.

The checked criterion does not by itself prove connectedness,
simple connectedness/global form, the order-three center, the actual
compact Spin(10) inclusion or oriented group branching. A group normalizer
may contain unwanted components and must not simply be renamed compact E6.
The [realization contract](../GUT/E6_MATRIX_PROTOTYPE.md#compact-carrier-acceptance-contract)
and its cost-review gate remain in force; M2-M5 are still open.

## 7. Sources and verification

### Verification

The persistent [audit](../../../../../Math/LieGroups/E6/Audit/AuditMatrixNormalizer.lean) is
imported by `GUT.lean` and checks 26 declarations using only `propext`,
`Classical.choice`, and `Quot.sound`. Concrete type checks cover the actual
commutant, both normalizer equivalences and the real dimension.

Negative controls show:

- `I` normalizes `L` but is not in `L`;
- `i I` is skew-Hermitian and normalizes `k` but is not in `k`, so the trace
  restriction is essential even on skew-Hermitian matrices;
- a Cartan matrix commutes with every Cartan generator but is not scalar,
  so Cartan commutation alone is insufficient.

Targeted: **3823 jobs / 26 axiom reports**, all four new Lean modules
warning-free. The ten existing Python tests pass; Python is outside the
proof trust boundary. Full regression is recorded in
[historical verified baseline](../../../../topics/proof-program-context/checkpoints/verified-baseline.md).

```sh
lake build Math.LieGroups.E6.Audit.AuditMatrixNormalizer
lake build
python3 -m unittest discover -s tools/e6 -p 'test_*.py'
```

Disposable logs: `.lake/e6-0f-audit.log` and `.lake/e6-0f-full-build.log`.
Lean sources and this record are tracked; dependency pins are unchanged.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
