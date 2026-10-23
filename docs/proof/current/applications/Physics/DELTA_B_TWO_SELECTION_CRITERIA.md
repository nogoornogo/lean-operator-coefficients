# Specified Six-Quark Residual Selection Criteria

## Result

For one-generation complex up/down flavor lines with arbitrary residual group H,
the independent right-quark degree `(2,4)` physical sector is allowed iff the
character `(up(g)1)^2 (down(g)1)^4` is identically one. It is forbidden iff this
condition fails. In the neutral case the sector is linearly equivalent to
`Fin 2 → ℂ`, and explicitly to `ℂ × ℂ`, with finrank two.

Sources: [scalar classification](../../../../../Physics/StandardModel/Operators/BaryonTwo/Coefficients/DeltaBTwoScalarSelection.lean),
[cyclic specialization](../../../../../Physics/StandardModel/Operators/BaryonTwo/Coefficients/DeltaBTwoCyclicSelection.lean),
[strict audit](../../../../../Physics/StandardModel/Operators/BaryonTwo/Coefficients/Audit/AuditDeltaBTwoSelection.lean).

## Inputs And Assumptions

Both flavor carriers are ℂ. The group H is arbitrary; compactness, continuity
and finite order are unnecessary for the scalar theorem. The underlying
gauge/spinor, right-handed species and degree remain those of the existing
`DeltaBTwoModelInterface.ModelSector`. The theorem does not classify other
six-quark patterns. Individual up/down actions need not be trivial.

For cyclic charges, `N : ℕ` and `[NeZero N]` are supplied. Use the proved
faithful character on `Multiplicative (ZMod N)`. Charges u,d belong to physical
u_R,d_R carriers, not their conjugates. Actual-field applications supply
the existing `Inputs` equivariant identifications; these are not derived spectra.

## Proof Structure And Inverses

`scalar_map` identifies any scalar-line action with multiplication by its
value on one. `slot_action` and `residual_action` prove that the ordered
heterogeneous six-linear coefficient transforms by the degree-weighted total
character. This proves necessity from a nonzero evaluation and forces every
coefficient to vanish when the character is nonneutral.

Under neutrality, `coefficientEquiv` retains exactly the same gauge/spin and
typed exchange constraints and the same underlying multilinear coefficient.
It changes only the residual invariance proof, identifying the space with
the already proved trivial-residual scalar space. `twoProbeEquiv` composes
this with the independent physical-sector equivalence and established
normalized two-probe extraction. `inverse_twoProbes` and
`reconstruct_twoProbes` prove both inverse identities; `pairEquiv` gives
the literal pair output. No 25-coordinate unrestricted space is substituted.

`onFieldsTwoProbeEquiv`, `allowed_onFields_iff` and `forbidden_onFields_iff`
transport these results through the supplied actual-field identifications.
The existing general constrained-Hom classification remains unchanged.

## Cyclic Criteria And Controls

Mathlib's faithful character theorem gives allowance iff `2u+4d=0` in ZMod N,
and prohibition iff `2u+4d≠0`. `simultaneous_iff` and
`simultaneous_forbidden_iff` combine this with the existing full signed
dimension-six four-family prohibition and neutral-Higgs LLHH allowance.

- Z2 quark parity `(q,u,d,l,e)=(1,1,1,0,0)` forbids all four Delta-B-one
  families, allows LLHH and allows this six-quark sector.
- Z5 charges `(1,1,0,0,0)` give four nonzero family charges `(2,3,3,2)`,
  neutral LLHH, and six-quark charge 2; thus both specified baryon sectors
  are forbidden.
- Trivial charges and all order-one assignments allow this six-quark sector.
  They do not satisfy the simultaneous Delta-B-one prohibition condition.

## Boundaries And Verification

These are coefficient-space statements, not UV generation, quantum exactness,
anomaly cancellation, Yukawa compatibility or rate predictions. No claim
is made about all Delta-B-two operators or arbitrary-generation neutrality
being sufficient. No external literature premise is added.

The persistent audit checks standard axioms only, transitively. Builds and
repository checks are recorded in the [topic](../../../../topics/delta-b-two-selection-criteria/README.md).
