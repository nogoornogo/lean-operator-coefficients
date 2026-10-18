# E6 Matrix Prototype and Realization Contract

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

**Follow-up:** [E6-0c](../Math/E6_LIE_CERTIFICATE.md) now proves the generated matrix
Lie dimensions 78/45, span equality and matrix D5 inclusion. The external
candidate language below records the E6-0b checkpoint; the compact/global
contract remains open. [E6-0d](../Math/E6_GECK_COMPARISON.md) now identifies these
matrix Lie algebras with the scalar-extended Geck carriers, preserving
the numbered generators; it does not close the compact/global contract.
[E6-0e](../Math/E6_COMPACT_REAL_FORM.md) proves real dimensions 78/45 and actual
complexification Lie equivalences for the skew-Hermitian real forms.

**E6-0b is complete as a bounded prototype, not as a compact E6 theorem.**
The [library audit](../../../../topics/e6-global-topology/decisions/E6_FEASIBILITY.md) remains the source for missing bridges
M1-M5. This milestone checks concrete adjoint equations, special-unitary
exponentials, and D5 invariant coordinate blocks. A finite Lie-basis candidate
has been generated externally, but has not been certified by Lean.

### Kernel-Checked Results

The matrices are the pinned TauCeti integral minuscule matrices, extended
entrywise to complex scalars. No replacement representation is postulated.

| Module | Checked result |
| --- | --- |
| [CompactGenerators](../../../../../Math/LieGroups/E6/Minuscule/CompactGenerators.lean) | `E_i^* = F_i`, `H_i^* = H_i`; `X_i = E_i - F_i`, `Y_i = I(E_i + F_i)`, and `Z_i = I H_i` are skew-Hermitian and traceless |
| [CompactExponentials](../../../../../Math/LieGroups/E6/Minuscule/CompactExponentials.lean) | For every real `t`, each `exp(t X_i)`, `exp(t Y_i)`, and `exp(t Z_i)` belongs to actual `SU(27)`; uses the existing determinant-exponential theorem |
| [D5Blocks](../../../../../Math/LieGroups/E6/Minuscule/D5Blocks.lean) | Deleting E6 node 0 gives the D5 Cartan submatrix; actual invariant coordinate subspaces have dimensions 16, 10, and 1 |
| [AuditMinusculeCompact](../../../../../Math/LieGroups/E6/Audit/AuditMinusculeCompact.lean) | Concrete type checks, negative controls, and a standard-axiom allowlist for the 38 listed declarations |

The D5 node map is `[5, 4, 3, 1, 2]`. The integral grading is
`q(w) = 4 w_0 + 3 w_1 + 5 w_2 + 6 w_3 + 4 w_4 + 2 w_5`.
Its coefficients pair with the E6 Cartan columns as `[3, 0, 0, 0, 0, 0]`.
Every minuscule weight has grade `1`, `-2`, or `4`, with counts `16`, `10`,
and `1`, respectively. D5 reflections preserve this grade; off-block entries
of all retained `E/F/H` generators vanish.

`gradeSpace q` is a genuine submodule of `Fin 27 -> Complex`, with a linear
equivalence to its selected coordinates and a proved finrank. The three
coordinate projections reconstruct every vector; unequal-grade subspaces
have zero intersection. Retained complex and compact generators preserve
them. The grade-4 coordinate is annihilated by every retained generator.
These statements are stronger than a count of weights, but do not yet give
an action of the repository's compact Spin(10) group.

The only D5-dominant rows are 0, 1, and 12. Their labels, in the displayed
D5 numbering, are `0`, the fourth-index fundamental label (a spinor label),
and the zeroth-index fundamental label (the vector label); their grades are
`4`, `1`, and `-2`. This finite label check does **not** prove irreducibility,
highest-weight classification, or the orientation of the existing compact
half-spin model under its SU(5) inclusion.

Negative controls check that `E_0` is not self-adjoint and that the omitted
E6 root genuinely mixes grades 4 and 1. Thus the D5 block conclusion is not
silently asserted for all E6 generators.

### Historical E6-0b Decision

The finite certificate and Lie comparison below are now completed as E6-0c/d.
At that checkpoint, the proposed next step was the bounded real/global-bridge
audit. The later result and retained external-input boundary are recorded in
[the owning topic](../../../../topics/e6-global-topology/README.md). The instructions
below describe the historical decision, not a current work queue.

**Continue finite Lie-algebra certification before attempting general
compact-group foundations.** The certificate sizes make a dedicated
Lean checker a concrete next experiment (E6-0c). Its acceptance criterion
is a proved generated-span/dimension theorem, with the comparison to the
pinned E6/D5 Lie algebras explicitly proved or explicitly left open.
Do not interpret successful finite certification as completion of M2-M4.

The earlier 1-3 workday E6-0b estimate applied only to this prototype. An
additional few focused workdays is a provisional estimate for the finite
checker, not a guarantee: kernel evaluation and the generated-subalgebra
bridge are unmeasured. The actual compact/global step remains the dominant
weeks-to-months risk if it requires new general foundations. There is still
no defensible completion estimate for all E6-1. Review that cost before
starting general integration or reductive-group infrastructure.

## 2. Inputs and conclusion

### Compact-Carrier Acceptance Contract

**Deferred full-realization contract.** This contract is retained for a
possible simply connected E6 construction, not as the exit condition of
the now-completed E6-0 audit or as the minimal input of the shared no-go
theorem. The [endpoint-first plan](../../../../topics/e6-global-topology/plans/E6_ENDPOINT_PLAN.md) separates those
questions. No unresolved clause is marked proved by deferring it.

The following are **obligations, not fields assumed by a completed theorem**.
Item 1 is discharged by [E6-0d](../Math/E6_GECK_COMPARISON.md), and item 2 by
[E6-0e](../Math/E6_COMPACT_REAL_FORM.md); items 3-6 remain open. This specifies what
E6-1 must supply before using the compact-group name.

Follow-up through [E6-0n](../Math/E6_TANGENT_LIE_ALGEBRA.md) constructs an actual
connected compact Lie-group candidate and identifies its geometric tangent
Lie algebra with the real form. Thus item 3's local geometric realization
is checked; its global-form, exact-center and simple-connectedness clauses
remain open.

1. **Actual Lie realization.** Construct the complex matrix Lie algebra
   generated by the pinned `E/F/H`, and prove an E6 Lie equivalence compatible
   with the simple generators. Prove the retained D5 realization and its
   inclusion. **Completed:** finite certificates plus the generator-preserving
   Geck comparison discharge this complex Lie-algebra part of M1.
2. **Compact real form.** Identify the relevant real skew-Hermitian
   subalgebra and prove that its complexification is the Lie algebra in
   item 1. **Completed:** the actual fixed subalgebras of `X -> -X^H` have
   real dimensions 78/45 and complexify to the pinned E6/D5 Geck carriers,
   compatibly with the D5 inclusion. Their elements exponentiate into
   SU(27). Equality with the real Lie span of the 18 displayed generators
   is not a separate result of this milestone.
3. **Global compact group.** Construct an actual connected compact group
   with this Lie algebra and a faithful continuous unitary 27 action.
   Identify the simply connected global form, by a proved root-datum/global
   comparison or equivalent construction, including the order-three center
   and its action. A Lie-algebra isomorphism alone does not distinguish
   global quotients. If using the closure in SU(27) of the subgroup generated
   by the checked exponentials, prove that closure has exactly the intended
   Lie algebra and global form. Closedness/compactness by construction does
   not discharge this requirement; closure can enlarge a Lie subgroup.
4. **Actual compact Spin inclusion.** Construct a continuous injective
   homomorphism from `GUT.CompactSpin.Group10`, with proved compatibility
   with the retained D5 generators and the chosen SU(5) chain. Lie inclusion
   alone does not prove its existence, injectivity, or finite-center kernel.
   If using the larger subgroup, handle `(Spin(10) x U(1))/Z4` explicitly.
5. **Actual 27 branching.** Relate the continuous 27 restriction to the
   repository's oriented half-spin 16, realified vector 10, and singlet,
   by intertwiners or a proved character identity. Prove the needed SU(5)
   orientation rather than choosing it from the dimensions alone.
6. **Physical endpoint and inhabitant.** Apply the existing conditional
   standard-chain theorem, and separately derive the positive exact dual
   SM target for an actual finite-dimensional source. Retain the ordinary
   Abelian and symmetric-mass scope; this is not an amplitude or vacuum
   selection theorem.

An independent identified compact E6 construction is an acceptable
alternative to the closure route. Neither route is implemented here.

## 4. Proof structure

### External Certificate Experiment

[Reproducible tools](../../../../../tools/e6/README.md) export the pinned data using
Lean-checked weight-coordinate entry formulas, then use Python's exact
`Fraction` arithmetic. No floating-point rank test, CAS package, dependency
upgrade, or restricted third-party source is used.

| Candidate | Basis size | Nonzero Cartan eigenlabels | Zero-weight dimension | Nonzero basis entries | Generator-closure equations |
| --- | ---: | ---: | ---: | ---: | ---: |
| E6 | 78 | 72 | 6 | 504 | 936 |
| D5 | 45 | 40 | 5 | 300 | 450 |

Each nonzero eigenlabel occurs once. The candidate spans are transpose-stable;
the D5 candidate also preserves the three grades. Output includes bracket
provenance, normalized pivot rows and their basis coefficients, and exact
generator-closure coordinates (284 and 156 nonzero coefficients). The
generator verifies coordinate reconstruction and rejects unexpected ranks.
The generated input is 1,987 bytes; the combined pretty-printed witness JSON
is 276,607 bytes. Six arithmetic/negative-control unit tests pass.

**All numbers in this table are external computation results, not Lean
dimension or root-system theorems.** A failed or malicious export/checker
cannot change the formal results above. In particular, a Cartan eigenlabel
is not automatically an identified root of the pinned Geck algebra.

A finite formal checker can verify provenance, independence, and closure
under the simple generators. A Jacobi/induction lemma must then connect
these facts to the generated Lie subalgebra. Equality with a span of 78
matrices still needs an actual root/bracket-compatible comparison with
Geck's E6, or a different proved E6 identification. The Serre-to-Geck
surjection alone still does not prove descent of the 27 representation.

## 7. Sources and verification

### Verification

```sh
lake build Math.LieGroups.E6.Audit.AuditMinusculeCompact
lake build
```

The prototype audit is imported by `GUT.lean`. The external tools are not.
The finite equalities use kernel reduction, not `native_decide` or
compiler-trusting axioms. Build totals and the latest regression record
are maintained in [COMPLETED](../../../../topics/proof-program-context/checkpoints/verified-baseline.md).
Generated JSON and logs under `.lake` are disposable; all source proofs,
tools, and this contract are tracked.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
