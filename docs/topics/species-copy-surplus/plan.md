# Frozen Proof Plan

## Mathematical Statement

H is an arbitrary group. R is a nonzero, finite-dimensional irreducible complex
H-representation. Each species i has its own finite-dimensional complex
H-representations A_i and C_i, with A_i semisimple. C_i need not be semisimple.
Mass maps M_i:A_i→C_i are arbitrary intertwiners. No compactness, continuity,
unitarity or finiteness of H is assumed.

Use the computable algebraic inlet

```
dim_C IntertwiningMap(R,A_i) > dim_C IntertwiningMap(R,C_i)
```

for every participating species. This measures copies of the selected R and
is not merely dim A_i > dim C_i. The initial theorem uses Hom dimensions
directly; an identification with representation multiplicities is optional
presentation/construction work, not an unproved Schur premise.

Target: for arbitrary such maps, R embeds and splits in every actual kernel.
The embeddings may differ and need not pick the same coordinate direction.
First prove this for a finite family, then specialize to Q,uc,ec. A single
common R is a sufficient condition, not a necessary characterization of all
allowed qque tensors.

## Phase 1 — Surplus To Common Kernel Splits

Construct postcomposition Hom(R,A_i)→Hom(R,C_i). Identify its kernel with
Hom(R,ker M_i), then use rank-nullity to obtain a nonzero map into the kernel.
Irreducibility makes it injective; source semisimplicity makes the actual kernel
semisimple and supplies a splitting. Reuse existing module/representation
transports. Do not assume a common light subspace or a kernel constituent.

Deliverables: the per-map theorem and finite-family corollary, explicit
hypotheses and strict transitive audits in Math. Target names/paths in the
interface register are provisional, to be checked against source APIs.
Stop only if a theorem-level prerequisite requires a new foundational scope;
ordinary finite-dimensional Hom/kernel and splitting helpers are within scope.

## Phase 2 — Original Mass And Physical Qque

Generalize the existing Species bridge to independent A_i,C_i. Keep the actual
field representation rho and original invariant symmetric mass B. Each species
supplies an injective full-sector map and a dual-field map with the commuting
mass square B∘embed=dualField∘(id_gauge tensor M_i). These are structural inputs,
not certificates that the participating fields are already light.

Derive actual light embeddings from the kernels, B-radical membership, restricted
ambient action and a physical qque exterior coefficient using Phase 1 and the
existing common-split spinor construction. Q uses its left carrier; right-handed
u/e use duals of the actual uc/ec ranges. Residual action on spinors remains
trivial. Do not replace this with an untyped tensor or charge-only witness.

Deliverables: a fixed-B realization theorem and an all-B wrapper when realization
is derived for every invariant symmetric mass on a fixed field/action model.
Keep the existing common-S/T API and its checked consumers unchanged. The shared
bridge may retain arbitrary actual F; finite F is required only by any constructor
that actually needs it. Stop before whole-radical extension or global descent.

## Phase 3 — Derive Species Mass Blocks Generically

Input a specified SM-cover × H decomposition of the original field carrier into
Q,uc,ec sectors, their dual gauge partners and an additional sector Z. Permit
different copy representations and counts. Supply or derive exact gauge
orthogonality/NoPairings conditions excluding same-side and unwanted cross-sector
bilinears, and the factorization interface for each allowed gauge pairing.
The decomposition and pairing conditions are model data; light membership,
Dirac normal form and mass squares must be conclusions.

For every invariant symmetric B, extract the residual intertwiners M_i and
prove the Phase 2 squares. Neutral/self-dual Z may contain Majorana masses when
it cannot pair with the selected species; do not impose a Dirac form on the
whole mass. Use existing SM pairing and BipartiteNormalForm interfaces. Freeze
any required finite carrier or Schur/factorization hypotheses explicitly before
implementation. No stronger result follows from a group embedding alone.

Deliverable: a reusable constructor for supplied SM decompositions, independent
of SU(5), PS or any UV group. If full general tensor factorization requires a new
foundation, close this phase with a precise feasibility boundary and retain the
proved Phase 2 bridge; do not silently assume the desired normal form. The
bounded routes are existing factorization APIs and a finite-copy coordinate
constructor. Do not restart the investigation under a renamed helper project.

## Controls And Acceptance

- Trivial H, Q:3→2, uc:3→2, ec:1→0: common R=trivial one-copy, independent
  kernels. This is a supplied SM block control, not a UV parameter certificate.
- Minimal chiral dictionary, species n→0: arbitrary neutral-sector symmetric
  mass must not affect selected light embeddings under pairing orthogonality.
- Positive total dimensions but disjoint residual constituents: no shared-R
  surplus is inferred. Distinct B/L or parity actions remain negative controls.
- Equality or reverse Hom dimensions must not be claimed to prohibit qque;
  zero/tuned masses can still leave light components. Surplus is sufficient.

Run focused builds, persisted strict transitive axiom/import audits, layout,
one serialized full build, and meaningful exact controls at proof milestones.
Update Math/Physics ledgers and general dossiers from actual proved statements.
Model records may receive linked applications only after their stated supplied
inputs are met. No new coverage row implies a verified UV branching or matching.

The completion condition is the verified general kernel and actual-range
physical bridge, plus the generic constructor or its explicitly recorded bounded
feasibility stop. Changes to physical scope, dependency pins or foundational
boundaries require user judgment. No proof implementation is included in the
planning checkpoint. Integration into master is not authorized for this topic.

## Exclusions

Coefficient generation, UV matching, cancellations of exchange amplitudes,
nonlinear/all-loop stability, post-EW exact mixing, rates and phenomenology are
outside the topic. No work package for generated coefficients is opened here.
