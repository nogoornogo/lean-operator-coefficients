import Physics.FieldTheory.Mass.Algebra.InvariantMassProtection
import Physics.FieldTheory.Mass.Algebra.LightInheritanceBoundary
import Lean.Util.CollectAxioms

open Physics Physics.InvariantWeylMass Physics.InvariantMassProtection

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
    ``Physics.InvariantMassProtection.cross,
    ``Physics.InvariantMassProtection.block,
    ``Physics.InvariantMassProtection.block_extends,
    ``Physics.InvariantMassProtection.cross_block,
    ``Physics.InvariantMassProtection.radicalMap,
    ``Physics.InvariantMassProtection.radicalMap_injective,
    ``Physics.InvariantMassProtection.preserves_iff,
    ``Physics.InvariantMassProtection.universal_iff_restriction,
    ``Physics.InvariantMassProtection.universal_of_hom_zero,
    ``Physics.InvariantMassProtection.universal_iff_hom_zero_of_retraction,
    ``Physics.InvariantMassProtection.universal_iff_hom_zero,
    ``Physics.InvariantMassProtection.light_semisimple,
    ``Physics.InvariantMassProtection.universal_iff_no_common,
    ``Physics.InvariantMassProtection.family_iff,
    ``Physics.InvariantMassProtection.exists_lifting_iff_common]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Invariant mass protection: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Invariant mass protection: {declarations.length} strict axiom checks passed"
