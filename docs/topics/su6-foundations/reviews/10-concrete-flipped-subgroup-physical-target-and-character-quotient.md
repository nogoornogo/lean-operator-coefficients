# concrete flipped subgroup, physical target, and character quotient

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Reviewer/tool: Codex with Lean/Lake kernel checks; the configured local LLM
  endpoint timed out and was not used for conclusions in this pass
- Version: Lean 4.33.1, Lake 5.0.0, mathlib v4.33.1
- Scope: concrete flipped subgroup, physical target, and character quotient

### Claim checked

The global form `U(3) x SU(2)` embeds injectively in `SU(6)` by
`(A,B) |-> diag(A,B,det(A)^-1)` and lifts the full flipped torus.  The five
physical field representations `Q`, `Uc`, `Dc`, `L`, and `Ec`, minus their
duals, have exactly the canonical one-generation Laurent character.  Hence
their whole-group virtual character is outside the restriction image of every
finite virtual `SU(6)` representation, both before and after quotienting
finite virtual presentations by character equality.

### Result

- [x] confirmed
- [ ] counterexample found
- [ ] proof gap found
- [ ] assumption missing
- [ ] inconclusive

### Lean witnesses

- `FlippedSMGroup.embedding_injective`
- `FlippedSMGroup.flippedTorusLift`
- `FlippedSMTarget.target_character_torus`
- `FlippedSMTarget.no_flippedSMTarget_characterEquivalent_restriction`
- `FlippedSMTarget.flippedSMTarget_character_not_mem_restrictionImage`
- `CharacterQuotient.restriction`
- `CharacterQuotient.flippedSMTarget_not_mem_quotientRestrictionImage`
- `AuditD2D3.audit7_concrete_target_not_mem_virtual_character_quotient_image`

The full build completed successfully with 3677 jobs.  Public theorem axiom
audits reported only `propext`, `Classical.choice`, and `Quot.sound`.

---
