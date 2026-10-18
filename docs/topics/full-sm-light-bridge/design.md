# Proposed Connection Theorem

Status: design, not an implemented theorem. Symbols below are mathematical
interfaces, not checked Lean declarations. Source assumptions require approval
before implementation; the current checked theorems remain unchanged.

Update: the user approved the [separated light-action route](implementation.md).
The original-matter mass-invariance input below is now an optional sufficient
constructor, not a premise of the connection core. Keep this file as the
original route comparison; current implementation status is in that record.

## Missing Obligations

Write S for `StandardSMGaugeTensor.GaugeGroup`, the covering product
SU(3) x SU(2) x Circle, and K for the actual radical of the given mass form.
The four monitored weight spaces are not intrinsically SM particle
multiplicity spaces: a weight can occur inside another SM irreducible.

1. K must carry an S action compatible with its existing torus and H actions.
2. The source target must identify residual representations in the Q,
   up and electron SM isotypic components of K.

An S-invariant mass solves the first obligation, not automatically the second.
Equality of dimensions or four torus indices does not identify SM multiplets.

## Proposed Inputs

Retain the compact continuous-H route's finite-dimensional complex matter,
ambient action `rho : Representation (G x H) E`, torus map j, torus unitarity,
symmetric T x H invariant mass B, two actual conjugations, four local target
conditions, and continuous nonzero finite-dimensional Q target P0. Strict
commutation with H and current physical scope boundaries are retained.

Add a jointly continuous action gamma of S x H on the same E, with

```text
gamma restricted along (PhysicalTorus.gaugeHom x id_H)
  = (rho restricted along (j x id_H))
      restricted along (PhysicalTorus.toTorus x id_H).
```

This is equality of actions on the physical covering torus, not identity of
two coordinate types. Require B.form to be gamma-invariant. The full-SM
mass must use exactly B.form, not a new form with a conveniently chosen
kernel. The diagram also fixes H by evaluation at the identity torus element.

An actual homomorphism i:S -> G with `i.comp gaugeHom = j.comp toTorus`
is a sufficient adapter for gamma. Neither injectivity nor factorization
through SU(5) is required by this generic interface. Continuity of gamma
must still be supplied or derived; continuity of H alone is insufficient.

Preservation of K is weaker than invariance of the whole form. Full-SM mass
invariance is the recommended source-level sufficient condition, not claimed
necessary. It does not assert an exactly-SM vacuum stabilizer or G-invariance.

Let R_Q be `quark`, R_U be `upRight.dual`, and R_E be
`electronRight.dual`: these are all left-handed gauge representations.
For a gauge irreducible R define H representations

```text
M_R = Hom_S(R, K),       N_R = Hom_S(R.dual, K),
(h . f)(v) = K(1,h)(f(v)).
```

The proposed local source package adds, for a = Q,U,E and all h in H,

```text
character(M_Ra)(h) - character(N_Ra.dual)(h) = character(P_a)(h).
```

P_Q=P0, P_U=P1, P_E=P4 are the same targets as in the four-weight input.
The existing conjugation theorem equates their characters. Only P0 needs
to supply the continuous finite-dimensional nonzero target for quotient
extraction. Do not silently impose continuity on unused down/lepton targets.

These are additional SM-resolved spectrum data, not consequences of the
four-weight hypothesis. They do not assume an operator, common quotient
or splitting. Verifying them for a physical model remains a source obligation.

## Recommended Route: Isotypic Extraction

1. Package the same form as a symmetric mass for gamma. Its kernel is an
   S x H subrepresentation. Identify the kernel, including H and physical-
   torus actions, with the original radical K.
2. Give M_R and N_R finite-dimensional continuous H structures. Reuse
   `ProductFactorization` postcomposition/evaluation. Transport continuity
   from the evaluation-image model or prove it on linear maps; do not
   independently assume multiplicity continuity.
3. Extract a nonzero irreducible quotient W of P0. Rearrange the three
   indices as `chi(M_Ra) = chi(N_Ra.dual) + chi(P0)`.
   Compact character positivity and semisimplicity give split surjections
   M_Ra -> W. Existence and splitting must both be proved.
4. Evaluation embeds R_a tensor M_Ra into K. Its image is the actual
   left-handed isotypic field. Restrict the injective evaluation to its
   image; do not assume K irreducible or evaluation onto K.
5. Obtain right-handed up/electron fields in K.dual. Dualizing an inclusion
   gives a surjection, not the needed inclusion. Derive an S x H equivariant
   splitting by compact complete reducibility, dualize it, and use the
   finite-dimensional bidual/tensor equivalences.
6. Apply `QqueSpinorExterior.exists_on_fields` with a=M_Q, b=M_U, d=M_E.
   One Q identification supplies both Q slots. Reuse the nonzero exterior
   witness and spinor/gauge invariance.

The conclusion concerns actual participating field subspaces and their sum,
as in the existing endpoint. Extending a coefficient to the entire radical
plus dual is not silently substituted for this statement. Auxiliary invariant
inner products may be chosen, but all maps return to the original radical.

## Alternative: Reconstruct The Old Adapter

`Decomposition` identifies particle multiplicities with entire selected
weight spaces L0, L3, L8, L14. This fits a clean SM spectrum but is needlessly
restrictive for arbitrary radicals.

A diagnostic mathematical example is a standard light generation plus
X + X.dual, with X=(3,4)_(6Y=1), the weak spin-3/2 representation, and
trivial residual action. Its weak weights include doublet weights. It adds
vectors at Q weights but no Q irreducible; its dual index cancels. Thus the
Q multiplicity cannot be identified with the enlarged entire Q weight space.

This diagnoses the attempted inference to the old adapter, not a failure of
the qque theorem. The example is not Lean-formalized here, and no ambient-G
realization satisfying the conjugation hypotheses has been constructed.
Do not report it as a counterexample to the complete source theorem.

One could assume no contaminating irreducibles and recover the old adapter.
Direct isotypic extraction instead tolerates unrelated light components and
is recommended. Do not develop both routes in parallel.

## Stronger Source Wrapper

A later global interface can require a full S x H character identity:

```text
chi_K(s,h) - chi_Kdual(s,h)
  = sum_a [chi_Ra(s) chi_Pa(h) - chi_Ra.dual(s) chi_Pa.dual(h)].
```

Here the sum runs over the five usual left-handed SM species. Require actual
finite-dimensional continuous targets for this wrapper and record that
stronger input. Compact character orthogonality should extract the three
species indices. Physical-torus restriction and faithful weight-character
comparison should recover the monitored indices. Neither is proved here.

An S x H invariant symmetric mass already preserves the full dual character
index, so this identity may be supplied on original matter and transported
to K. Additional sectors self-dual as S x H representations are invisible
to it. Being vectorlike only under S is insufficient if H actions do not
pair dually. Nonzero-index singlets need an explicit allowed remainder;
they are not covered by the displayed equality as written.

This wrapper can remove duplicated target inputs, but is a stronger global
specification. It is not proof that arbitrary torus targets lift, and it
is not required for the local connection theorem.

## Milestones And Gates

| Step | Deliverable | Main risk / stop condition |
| --- | --- | --- |
| FSM-1 | Same-form SM mass, invariant radical, restriction/H agreement | Do not replace the original carrier/action |
| FSM-2 | Continuous multiplicities, evaluation-image equivalences, dual split embeddings | No irreducibility of whole K; retain compactness |
| FSM-3 | Concrete Q/up/e gauge irreducibility and dual/tensor identifications | Generic tools exist; concrete instances remain to prove |
| FSM-4 | Species indices -> common split quotient -> actual exterior qque; audits/controls | No projector, quotient or tensor-existence premise |
| FSM-5 | Separate full-SM character wrapper -> both local input packages | Character extraction and five-species separation are not a trivial adapter |

FSM-1 is high-confidence reuse. FSM-2 through FSM-4 are medium-to-high
confidence mathematically; the main Lean effort is topology on Hom spaces
and representation transport. Estimate FSM-5 after those interfaces compile.
No measured implementation time or completion date is asserted by this audit.

FSM-4 acceptance: focused builds, strict transitive axiom audits, full
`lake build`, layout/link checks and applicable exact qque regression tests.
Include a one-generation positive control and an extra self-dual light-sector
control. The existing concrete SU6 neutral-H mass is another source regression
candidate, not an already-built instance of this interface.

Check that SM invariance and species indices remain explicit inputs, that
continuity/splittings are derived, fields lie in the unchanged K or K.dual,
and exterior nonvanishing survives. Freeze any new prerequisite before coding.
