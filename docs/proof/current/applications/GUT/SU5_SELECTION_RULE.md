# SU(5) ordinary-Abelian selection-rule theorem

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Status: **LEAN-CHECKED**, SU5-5, stage 01. The SU5-1 through SU5-5
roadmap is complete in the scope below. This is separate from the SU(6)
mass/index theorems and does not change their assumptions.

## 2. Inputs and conclusion

### Statement

Retain `n > 0` copies of the actual complex SU(5) representations
`10 + bar5`, with the fixed standard SM embedding. Let any Abelian group
`H` act unitarily on this matter and commute exactly with the full SU(5)
action. Then its charge selection rule cannot prohibit every supported
signature in the declared dimension-six, Delta-B = Delta-L = 1 class.

The theorem constructs both `qque` and `duql` with actual field support
and trivial residual characters. It also constructs nonzero invariant
ordered internal tensors on their field ranges and contragredients, for
`((SU(3) x SU(2) x U(1))/Z6) x H`.

The public declarations are `SelectionRule.scoped_no_go` and
`SelectionRule.Model.selection_rule_obstruction` in
[SelectionRule.lean](../../../../../GUT/SU5/SelectionRules/SelectionRule.lean).
For arbitrary positive `n` and an actual `OrdinaryAction H n`, the former
proves:

```lean
¬ ForbidsEverySupportedDeltaBOne R ∧ Nonempty (OperatorWitness R)
```

The model inputs are only the positive generation count and the commuting
unitary action. Equal charges, field support, and tensor nonvanishing are
outputs, not assumptions. `oneGeneration H` constructs an inhabitant for
every Abelian `H`, with trivial residual action on the actual matter.

## 4. Proof structure

### Meaning of Support and Prohibition

`FieldSupported` requires an injective linear field map into the actual
matter, with the correct full SM gauge action and residual character.
For right-handed operator fields it requires the corresponding left-handed
conjugate field; the actual right-handed space is its dual. The proved
`rightSplit` and bidual equivalence justify this convention.

`SlotsSupported` permits a different charge-sector assignment at each of
the four positions. Thus the two Q fields in `qque` need not have equal
charges or come from the same generation. `slotCharacter` sums physical
charges with the right-handed minus signs and converts to an `H ->* Circle`
character. The prohibition predicate quantifies over **all** these
supported choices whose signatures pass the existing quantum-number and
contraction-plan checks. It does not demand SU(5) charge compatibility
as an extra premise.

To refute universal prohibition it suffices to select suitable sectors.
The theorem does not assert that every supported choice is neutral. A
finite-action audit explicitly exhibits both neutral and nonneutral
supported choices in the same source. No topology, finiteness, torsion-free
condition, or family universality is assumed for `H`.

### Dependency Chain

1. The actual embedding, exact central order-six kernel, and quotient image
   are proved in [SU5-2](../../inputs/GUT/interfaces/su5-embedding.md).
2. Actual defining/dual/exterior matter, full-group branching, continuity,
   unitarity, and constituent irreducibility are proved in
   [SU5-3](../../inputs/GUT/interfaces/su5-matter.md).
3. The full U centralizer and exhaustive Abelian character sectors derive
   the common multiplet charges and actual field injections in
   [SU5-4](../../inputs/GUT/interfaces/su5-source.md). There is no residual
   determinant-one restriction.
4. The shared charge cancellation and internal tensors give both neutral
   signatures and nonzero forms on these actual field ranges/duals.
5. `SupportedQuotient` proves that the whole central kernel acts trivially,
   descends the field/tensor actions, and proves exact covering pullback.
   The descended field action agrees with the actual SU(5) action through
   the injective quotient map. `SelectionRule` constructs the witness and
   refutes universal charge prohibition using it.

The final import closure is audited to exclude `GUT.SU6`. No anomaly
argument, virtual-index reconstruction, or bounded search is used.

## 6. Scope and limitations

### Boundaries

This is a retained-spectrum model, not a theorem for every SU(5)
representation or Lagrangian. Heavy vectorlike matter and its removal,
vacuum dynamics, and an exact-SM stabilizer are not derived here.

The legacy predicate name `IsPhysicalDeltaBOneOperator` means the declared
signature's quantum numbers and contraction plan pass their checks. It
does **not** certify a nonzero operator after Lorentz contraction and a
Grassmann quotient. The additional nonzero forms are ordered **internal**
tensors. There is no Wilson coefficient, amplitude, decay-rate, or lifetime
claim. Non-Abelian, gauge-normalizing/twisted, R, supersymmetric,
generalized, and non-invertible symmetry extensions are not included.

## 7. Sources and verification

### Verification

The [final audit](../../../../../GUT/SU5/Audit/AuditSelectionRule.lean) checks one
generation, the vacuous zero-generation exclusion, a nontrivial finite
order-two character with actual support, different per-slot choices,
the nonidentity kernel element, and inversion at the non-self-inverse
phase `i`. It retains the incompatible IR assignment and actual UV
commutation controls from the earlier audits.

The [declaration dossier](interfaces/su5-final.md) records commands,
axioms, and the full build. The
[Physlib candidate](../../../../topics/su5-geometry-upstream/candidate.md) is identified
separately; porting or submitting it is not part of the theorem's proof.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
