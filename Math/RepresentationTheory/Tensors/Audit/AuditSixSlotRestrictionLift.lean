import Math.RepresentationTheory.Tensors.SixSlotRestrictionLift
import Lean.Util.CollectAxioms

/-! Strict checks for the degree `(2,4)` restriction/reconstruction bridge. -/

set_option autoImplicit false

namespace Math.SixSlotRestrictionLift.Audit

open Representation SixSlotAlternation SixSlotSpeciesDegree

example {H A B : Type*} [Group H]
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (a : Representation ℂ H A) (b : Representation ℂ H B)
    (f : coefficients a b) (hf : HasDegree a b f) :
    coefficient a b ((1 / 48 : ℂ) • restriction a b f) = f :=
  reconstruct a b f hf

end Math.SixSlotRestrictionLift.Audit

run_cmd do
  let declarations := [
    ``Math.SixSlotAlternation.preservesPattern_card,
    ``Math.SixSlotAlternation.alternating_slots_of_preserves,
    ``Math.SixSlotSpeciesDegree.coefficient_hasDegree,
    ``Math.SixSlotSpeciesRestriction.slots_ext,
    ``Math.SixSlotRestrictionLift.restriction_preserves,
    ``Math.SixSlotRestrictionLift.alternating_restriction_slots,
    ``Math.SixSlotRestrictionLift.reconstruct]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Six-slot restriction: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Six-slot restriction: {declarations.length} strict transitive axiom checks passed"
