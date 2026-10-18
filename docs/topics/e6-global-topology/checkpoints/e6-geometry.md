# e6 geometry

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

- **E6-0p component scalar-center upper bound (stage 01):** differentiated
  actual exponential commutation and extended it to the complex algebra.
  The scalar commutant and SU determinant construct an injective center
  homomorphism into the 27th roots. The center is finite cyclic of order
  dividing 27; neither exact order nor all-root component membership is
  asserted. Targeted 4035 jobs / 128 reports (14 new); full 5470 jobs /
  2384 reports, standard axioms only. New modules warning-free; ten tests
  pass. See [scalar center](../../../proof/current/inputs/Math/E6_COMPACT_CENTER.md).
- **E6-0o global-form feasibility audit (stage 01):** inspected pinned
  integration, covering, group-scheme and Albert-algebra APIs. No direct
  simply connected identification of this candidate was found. Recorded
  concrete scalar-center and Cartan preflights separately from cubic
  invariance, global topology and general foundations, with a cost gate.
  Documentation-only; E6-0n remains the verified build baseline. See
  [global-form audit](../decisions/E6_GLOBAL_FORM_AUDIT.md).
- **E6-0n geometric tangent Lie-algebra identification (stage 01):**
  constructed the smooth injective matrix-units homomorphism and computed
  its differential. Reused the audited Lie functor and units commutator
  equivalence to identify the candidate's geometric tangent Lie algebra
  with the actual E6 real form. An explicit invariant-vector-field bracket
  theorem guards against substituting the model-space bracket. Targeted
  4031 jobs / 114 reports (11 new); full 5468 jobs / 2370 reports, standard
  axioms only. Both new modules are warning-free; ten tooling tests pass.
  Global form, exact center, simple connectedness and actual Spin inclusion
  remain open. See [tangent Lie algebra](../../../proof/current/inputs/Math/E6_TANGENT_LIE_ALGEBRA.md).
- **E6-0m actual tangent image (stage 01):** computed the matrix
  inclusion's manifold differential at one. It is injective, and its
  image is exactly the actual real form; tangent/model casts are explicit.
  Kernel-audited the pinned Lie functor and units commutator ingredients
  for the next bracket bridge. Targeted 4029 jobs / 103 reports (seven
  project declarations, four library ingredients); full 5466 jobs / 2359
  reports, standard axioms only. Both new modules are warning-free; ten
  tooling tests pass. Bracket/global identification remains open. See
  [tangent image](../../../proof/current/inputs/Math/E6_TANGENT_IMAGE.md).
- **E6-0l smooth connected compact candidate group (stage 01):** proved
  smooth injective matrix inclusion and a local matrix smoothness criterion.
  Actual matrix multiplication and real-linear conjugate transpose give
  smooth group operations and the `LieGroup` instance on the checked atlas.
  Targeted 3878 jobs / 92 reports (12 new); full 5449 jobs / 2348 reports,
  standard axioms only. Both new modules are warning-free; ten tooling
  tests pass. Tangent Lie/global identification and actual Spin inclusion
  remain open. See [candidate Lie group](../../../proof/current/inputs/Math/E6_CANDIDATE_LIE_GROUP.md).
- **E6-0k translated smooth atlas (stage 01):** translated the checked
  exponential chart to every point of the existing connected compact
  candidate. Proved analytic transition formulas and a smooth manifold
  instance on the unchanged topology, with the actual dimension-78 real
  form as model. The ambient exponential derivative at zero is the
  real-form inclusion. Targeted 3863 jobs / 80 reports (14 new); full
  5447 jobs / 2336 reports, standard axioms only. New/extended modules are
  warning-free; ten tooling tests pass. Smooth group operations and
  tangent/global comparisons remain open. See [smooth atlas](../../../proof/current/inputs/Math/E6_SMOOTH_ATLAS.md).
- **E6-0j actual local exponential chart (stage 01):** constructed an
  open partial homeomorphism from the actual 78-dimensional real form to
  the connected compact candidate. The forward map is matrix exponential;
  its inverse is the ambient matrix logarithm on the entire target, with
  local analyticity there. Open neighborhoods and inverse laws are derived,
  not supplied. Targeted 3851 jobs / 66 reports (19 new); full 5445 jobs /
  2322 reports, standard axioms only. Three new modules are warning-free;
  ten tooling tests pass. Atlas/smoothness, tangent/global identification
  and actual Spin inclusion remain open. See [local chart](../../../proof/current/inputs/Math/E6_LOCAL_CHART.md).
- **E6-0i local real-form logarithm and exponential generation (stage 01):**
  proved the local converse to exponential conjugation preservation using
  the convergent operator logarithm. Local SU logarithms are skew-Hermitian
  and traceless; the E6 Lie-normalizer bound then gives actual real-form
  logarithms near the normalizer identity. Positive neighborhood radii are
  derived, not assumed. The identity component is open and equals the
  algebraic subgroup generated by real-form exponentials. The reused
  periodic scalar still refutes a global time-one converse. Targeted 3848
  jobs / 47 reports (25 new, 22 reused); full 5442 jobs / 2303 reports,
  standard axioms only. Five new modules are warning-free; ten tooling
  tests pass. Local chart/atlas and global identification remain open.
  See the [local-logarithm record](../../../proof/current/inputs/Math/E6_LOCAL_LOG.md).
- **E6-0h connected candidate and scalar-center control (stage 01):**
  constructed the normalizer's closed, compact, connected identity
  component and retained the exact all-time exponential criterion via
  continuous real-parameter curves. A generic scalar-normalizer lemma
  constructs a central element of exact order 27 in the full normalizer,
  excluding isomorphism to any group whose center has exponent dividing
  three. No membership of that scalar in the identity component is claimed.
  Pinned ambient matrix log/exp inverse identities are kernel-checked;
  subgroup chart/global APIs are separately source-audited. Targeted 3845
  jobs / 31 reports; full 5437 jobs / 2278 reports, standard axioms only.
  Five new modules are warning-free; ten tooling tests pass. Local real-form
  logarithm, manifold/global identification and actual Spin inclusion remain
  open. See the [component audit](../../../proof/current/inputs/Math/E6_IDENTITY_COMPONENT.md).
- **E6-0g closed compact matrix normalizer (stage 01):** constructed
  the actual closed compact subgroup of SU(27) preserving the real E6
  matrix algebra by conjugation. Reusable Banach-algebra, special-unitary
  and matrix-normalizer lemmas prove that its all-real-time exponential
  directions are exactly the existing 78-dimensional real form. Reused
  TauCeti's commutator-exponential identity and the E6-0f algebraic bound;
  no tangent or group-realization certificate is assumed. A periodic
  scalar counterexample shows that time one alone is insufficient.
  Targeted 3833 jobs / 22 reports; full 5428 jobs / 2247 reports, standard
  axioms only. Five new modules are warning-free; ten tooling tests pass.
  Manifold comparison, components/global form and actual Spin inclusion
  remain open; the subgroup is not named compact E6. See the
  [matrix-group milestone](../../../proof/current/inputs/Math/E6_COMPACT_NORMALIZER.md).
- **E6-0f scalar commutant and Lie-normalizer bounds (stage 01):**
  distinct Cartan weights and kernel-checked raising paths prove that
  matrices commuting with the twelve actual E6 root generators are scalar.
  A reusable normalizer derivation, mathlib's innerness theorem and the
  transferred Geck Killing form give an exact trace-zero complex normalizer
  bound. Real-form complexification gives the matching skew-Hermitian
  trace-zero bound; its ambient-matrix carrier is Lie-isomorphic to the
  prior real form and has real dimension 78. No irreducibility or normalizer
  certificate is supplied in the concrete result. Negative controls check
  the essential trace and root-generator restrictions. Targeted 3823 jobs /
  26 reports; full 5422 jobs / 2225 reports, standard axioms only. Four new
  modules are warning-free; ten tooling tests pass. The closed subgroup,
  exponential/tangent comparison and global form remain open. See the
  [normalizer milestone](../../../proof/current/inputs/Math/E6_MATRIX_NORMALIZER.md).
