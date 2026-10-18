import Physics.StandardModel.Operators.LightSMSpeciesQque
import Math.RepresentationTheory.Unitary.UnitarySubrepresentationOrthogonality
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Controls for actual-subspace transport, not claims that these independent
SM actions supply an ambient GUT source with both index packages. -/

namespace GUT.ActualLightFieldsAudit
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open StandardSMGaugeTensor QqueSpinorExterior
open UnitarySubrepresentationOrthogonality (rangeEquiv)
open scoped TensorProduct

local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup (Quark ⊗[ℂ] ℂ) := inferInstance

def flavor := Representation.trivial ℂ Unit ℂ
def leftQ := external quark flavor
def leftU := external upRight.dual flavor
def leftE := external electronRight.dual flavor

def ambient {X : Type*} [AddCommGroup X] [Module ℂ X]
    (extra : Representation ℂ (GaugeGroup × Unit) X) :=
  (leftQ.prod (leftU.prod leftE)).prod extra

theorem actual_subspaces {X : Type} [AddCommGroup X] [Module ℂ X]
    (extra : Representation ℂ (GaugeGroup × Unit) X) :
    ∃ Q : Subrepresentation (ambient extra),
      ∃ U E : Subrepresentation (ambient extra).dual,
        HasNonzeroAlternation (Q := Q.toSubmodule) (U := U.toSubmodule) (E := E.toSubmodule)
          Q.toRepresentation U.toRepresentation E.toRepresentation := by
  let base := Split.fst (leftQ.prod (leftU.prod leftE)) extra
  let sq := base.trans (Split.fst leftQ (leftU.prod leftE))
  let right := base.trans (Split.snd leftQ (leftU.prod leftE))
  let su := right.trans (Split.fst leftU leftE)
  let se := right.trans (Split.snd leftU leftE)
  let eqQ := (rangeEquiv sq.embed (Function.LeftInverse.injective sq.left_inv)).symm
  let eqU := (rangeEquiv su.dual.embed
    (Function.LeftInverse.injective su.dual.left_inv)).symm.trans
      (ExternalTensorDual.rightModelEquiv upRight flavor)
  let eqE := (rangeEquiv se.dual.embed
    (Function.LeftInverse.injective se.dual.left_inv)).symm.trans
      (ExternalTensorDual.rightModelEquiv electronRight flavor)
  let s := Split.ofEquiv (Representation.Equiv.refl flavor)
  exact ⟨sq.embed.range, su.dual.embed.range, se.dual.embed.range,
    exists_on_fields s s s _ _ _ eqQ eqU eqE⟩

def emptyExtra := Representation.trivial ℂ (GaugeGroup × Unit) (Fin 0 → ℂ)
def singlet := Representation.trivial ℂ (GaugeGroup × Unit) ℂ
def selfDualExtra := singlet.prod singlet.dual

def extraSelfDual : Representation.Equiv selfDualExtra selfDualExtra.dual := by
  let swap : Representation.Equiv selfDualExtra (singlet.dual.prod singlet) :=
    { toLinearEquiv := LinearEquiv.prodComm ℂ _ _
      isIntertwining' _ := rfl }
  exact swap.trans ((prodEquiv (Representation.Equiv.refl singlet.dual)
    (bidualEquiv singlet)).trans (dualProdEquiv singlet singlet.dual))

theorem one_generation :
    ∃ Q : Subrepresentation (ambient emptyExtra),
      ∃ U E : Subrepresentation (ambient emptyExtra).dual,
        HasNonzeroAlternation (Q := Q.toSubmodule) (U := U.toSubmodule) (E := E.toSubmodule)
          Q.toRepresentation U.toRepresentation E.toRepresentation :=
  actual_subspaces emptyExtra

theorem with_self_dual_extra :
    ∃ Q : Subrepresentation (ambient selfDualExtra),
      ∃ U E : Subrepresentation (ambient selfDualExtra).dual,
        HasNonzeroAlternation (Q := Q.toSubmodule) (U := U.toSubmodule) (E := E.toSubmodule)
          Q.toRepresentation U.toRepresentation E.toRepresentation :=
  actual_subspaces selfDualExtra

end
end GUT.ActualLightFieldsAudit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Actual-field audit imports {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.StandardSMIrreducibility.quark_irreducible,
    ``GUT.StandardSMIrreducibility.upRight_irreducible,
    ``GUT.StandardSMIrreducibility.electronRight_irreducible,
    ``GUT.StandardSMIrreducibility.upLeft_irreducible,
    ``GUT.StandardSMIrreducibility.electronLeft_irreducible,
    ``GUT.LightSMFieldExtraction.Fields,
    ``GUT.LightSMFieldExtraction.nonempty_fields,
    ``GUT.LightSMSpeciesQque.HasActualExterior,
    ``GUT.LightSMSpeciesQque.exists_actual_alternation,
    ``GUT.LightSMSpeciesQque.exists_actual_exterior,
    ``GUT.ActualLightFieldsAudit.actual_subspaces,
    ``GUT.ActualLightFieldsAudit.extraSelfDual,
    ``GUT.ActualLightFieldsAudit.one_generation,
    ``GUT.ActualLightFieldsAudit.with_self_dual_extra]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Actual-field audit: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Actual-field bridge: {declarations.length} strict axiom checks passed"
