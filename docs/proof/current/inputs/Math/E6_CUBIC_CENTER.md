# E6 Cubic and Exact Center

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

## 2. Inputs and conclusion

### Bounded Endpoint

**LEAN-CHECKED:** the center of the existing `compactIdentityComponent` has
cardinality three and is group-isomorphic to `rootsOfUnity 3 ℂ`.
The user's continuation request authorized this concrete
package, following the order-three lower bound in [E6_CENTER_THREE.md](E6_CENTER_THREE.md).
The group, its topology, the pinned matrices and all physical hypotheses
are unchanged.

This closes the exact-center input of the chosen global-form investigation.
It is not required by the already proved candidate selection-rule theorem,
and does not by itself establish simple connectedness or identify the
candidate with the intended global compact E6.

### Frozen Interfaces

1. An explicit nonzero homogeneous cubic on the actual minuscule 27,
   with kernel-checked infinitesimal invariance for the actual matrix Lie
   algebra. Any external computation produces data, not trusted evidence.
2. Invariance under real-form exponentials and hence the identity component,
   using the existing algebraic exponential-generation theorem. A finite
   Lie-level certificate alone is insufficient.
3. For a central scalar, cubic invariance forces `z^3 = 1`; combine this
   with the existing order-three element to prove the exact center size.

The allowed route is finite polynomial arithmetic, differentiation along
matrix exponentials, and the already established scalar commutant. Helpers
must serve these three interfaces. No dependency upgrade, assumed invariant,
Lie integration/classification library, or topology foundation is authorized.

## 6. Scope and limitations

### Acceptance and Exit

All three frozen interfaces are closed:

- [SparseCubicCertificate](../../../../../Math/LieAlgebras/SparseCubicCertificate.lean)
  proves soundness of monomial collection and the integer zero checker.
  Lists are certificate syntax, not a quotient-free claim of a faithful
  polynomial model. Their interpretation is an ordinary cubic function.
- [CubicInvariant](../../../../../Math/LieGroups/E6/Minuscule/CubicInvariant.lean) supplies 45
  signed monomials. Lean checks all 78 actual basis matrices, then uses the
  existing span equality for the full matrix Lie algebra. The function is
  nonzero: it equals one at the vector supported at coordinates `0,12,26`.
  For every scalar `z`, `cubic (z * v) = z^3 * cubic v` (scalar multiplication).
- [CubicExponential](../../../../../Math/LieAlgebras/CubicExponential.lean)
  differentiates the actual matrix-exponential orbit. Its derivative is
  zero by infinitesimal invariance, so the cubic is constant on the orbit.
  [CubicGroupInvariant](../../../../../Math/LieGroups/E6/Minuscule/CubicGroupInvariant.lean)
  uses the existing `CompactLocalLog` exponential-generation theorem to
  prove `cubic_invariant` for every element of the connected candidate.
- [ExactCenter](../../../../../Math/LieGroups/E6/Minuscule/ExactCenter.lean) uses the scalar
  commutant, cubic invariance and the nonzero witness to force `z^3 = 1`.
  `compactCenter_card` combines this upper bound with the previously
  constructed order-three element. `compactCenterEquivCubeRoots` gives
  the group isomorphism. `centralScalar27_not_mem` proves the full
  normalizer's order-27 element is outside the identity component, while
  its ninth power still belongs by the earlier theorem.

The candidate coefficient search used exact integer weight and generator
data. Neither that search nor its output is trusted: `cubic_checked`
reduces all infinitesimal equations in Lean's kernel against the actual
matrix basis. The group-invariance proof is essential; a finite table by
itself would not justify the center conclusion.

```sh
lake build Math.LieGroups.E6.Audit.AuditExactCenter
lake build
```

The [persistent audit](../../../../../Math/LieGroups/E6/Audit/AuditExactCenter.lean) checks 23
declarations with only `propext`, `Classical.choice`, `Quot.sound`. It
also rejects an incomplete cubic certificate and retains the distinct
full-normalizer/component tests. Targeted: **3884 jobs / 23 reports**.
Full: **5492 jobs / 2525 reports** (2524 lists and one axiom-free).
New modules are warning-free; no dependency or trusted axiom was added.

**Stop gate reached.** Simple connectedness and intended global compact
E6 identification remain open. Even this exact center does not supply a
maximal-torus/coroot-lattice to fundamental-group theorem or a global
covering with trivial kernel. No such foundational project is started by
this package, and the existing physical theorem's assumptions are unchanged.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
