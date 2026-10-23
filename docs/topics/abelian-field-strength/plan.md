# Frozen Free Abelian Contract

## Statements And Conventions

Use complex coefficients, `Fin 4` derivative directions, signature (+---), and
the existing actual SL(2,ℂ) Pauli vector action and its dual direction action.
There is one neutral bosonic field strength, no charged matter and no source.
Begin with the ordered-pair tensor source `V ⊗ V`, transported to labelled
Finsupp components. Impose the algebraic relations `F_ab + F_ba = 0`, including
the diagonal relations over ℂ. These are source vectors; physical coefficient
functionals belong to the dual. No classical field-index dictionary is assumed.

For basis indices, the differential source equations are

\[
M_b=\sum_a D_a F_{ab},\qquad
B_{abc}=s_aD_aF_{bc}+s_bD_bF_{ca}+s_cD_cF_{ab},
\quad (s_0,s_1,s_2,s_3)=(1,-1,-1,-1).
\]

This uses vector-source field indices and dual derivative labels; metric
transport is explicit. The combined seed includes antisymmetry, Maxwell and
Bianchi generators. Its relation module consists of all polynomial derivative
multiples. The source is defined directly in terms of field strength: proving
an exact potential/gauge-quotient presentation is excluded.

## Finite Deliverables

1. Construct actual tensor component and equation representations. Derive the
   metric intertwiner from the proved quadratic invariance and prove seed
   covariance, rather than assuming Lorentz stability of equations.
2. Instantiate the common relation module, quotient generators, commuting
   shifts and action. Prove every displayed family and derivative descendant
   zero, and derive the component wave equation and its descendants from the
   complete Maxwell/Bianchi system, not as a replacement premise.
3. Give two independent transverse null-symbol probes. They annihilate every
   relation and detect jets of arbitrarily high order before IBP. This does
   not classify physical helicities or prove a nonzero integrated invariant.
4. Instantiate the actual symmetric on-shell algebra through the common
   even interface (empty odd species), onto projection, exact EOM-kernel
   presentation, finite image grades and inverse equivariant EOM/IBP source
   and coefficient descent. No general EFT enumeration is required.

## Routes, Resources And Stops

Primary route: tensor basis transport, canonical vector/dual contraction and
metric intertwining; finite-basis multilinearity proves covariance. For the
wave consequence and probes use finite sums and polynomial evaluation.
Alternate route: explicit finite component matrices for the same maps and
equations, using proved basis reconstruction. Neither route may replace actual
covariance or a source connection by an external theorem parameter. A failure
of both routes requiring new independent foundations is a documented scoped
feasibility stop, not permission to change equations or broaden the project.

Retain dependency pins and default Lean heartbeat/recursion/kernel limits.
Heavy checks are serialized with four threads, 540 seconds per command and an
inherited 16 GiB per-process address-space guard. Persist strict transitive
standard-axiom/import audits and register all modules in the proper aggregate.
Require focused builds, full `lake build`, layout, links, topic index, portable
metadata and diff checks. Reconcile literature roles, proof dossiers and
assumption ledgers, review and commit. Checkpoints are not stops: continue
through the endpoint or an actual scope/authority stop. Leave the verified
child unmerged unless separately integrating within the recorded parent rule.

Excluded: non-Abelian covariant commutators, interactions/sources, potentials
and gauge exactness, de Rham/Poincaré theorems, analytic variational dynamics,
global topology, Hodge/helicity classification, amplitudes, matching, rates,
numerical evolution and new dependencies. An inspected Physlib theorem is not
a proved bridge to this source unless that bridge is constructed and audited.
