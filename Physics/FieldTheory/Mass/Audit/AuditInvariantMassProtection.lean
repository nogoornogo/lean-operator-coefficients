import Physics.FieldTheory.Mass.InvariantMassProtection
import Physics.FieldTheory.Mass.LightInheritanceBoundary
import Lean.Util.CollectAxioms

open GUT GUT.InvariantWeylMass GUT.InvariantMassProtection

theorem paired_control {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V) (x : V) (hx : x ≠ 0) :
    ¬ UniversallyProtected (SymmetricMass.zero rho) rho.dual := by
  intro h
  have hp := h (LightInheritanceBoundary.pairedMass rho)
    (LightInheritanceBoundary.restricted_mass_eq rho)
  have hn := LightInheritanceBoundary.light_not_preserved rho x hx
  exact hn.2 (hp ⟨x, hn.1⟩)

run_cmd do
  let declarations := [
    ``paired_control,
    ``GUT.InvariantMassProtection.cross,
    ``GUT.InvariantMassProtection.block,
    ``GUT.InvariantMassProtection.block_extends,
    ``GUT.InvariantMassProtection.cross_block,
    ``GUT.InvariantMassProtection.radicalMap,
    ``GUT.InvariantMassProtection.radicalMap_injective,
    ``GUT.InvariantMassProtection.preserves_iff,
    ``GUT.InvariantMassProtection.universal_iff_restriction,
    ``GUT.InvariantMassProtection.universal_of_hom_zero,
    ``GUT.InvariantMassProtection.universal_iff_hom_zero_of_retraction,
    ``GUT.InvariantMassProtection.universal_iff_hom_zero,
    ``GUT.InvariantMassProtection.light_semisimple,
    ``GUT.InvariantMassProtection.universal_iff_no_common,
    ``GUT.InvariantMassProtection.family_iff,
    ``GUT.InvariantMassProtection.exists_lifting_iff_common]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Invariant mass protection: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Invariant mass protection: {declarations.length} strict axiom checks passed"
