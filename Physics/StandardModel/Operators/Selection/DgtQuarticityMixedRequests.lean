import Physics.StandardModel.Operators.Selection.MixedSelectionPatterns

/-! Bounded existing-model consumers of indexed mixed requests. -/
namespace Physics.DgtQuarticityMixedRequests
set_option autoImplicit false
noncomputable section
open Math Representation SelectionCriteria MixedSelectionRequests

inductive DgtTarget where
  | baryon
  | dipole (i : Fin 2)
  deriving DecidableEq

/-- Both absolute B1/B2, all degrees, and each actual IR selector image. -/
def dgtDomain : DgtTarget → Type
  | .baryon => ∀ n m : ℕ, ComposableBLSupport.Input
      DgtFlavorRestriction.irFlavor DgtFlavorRestriction.irScalar
      ComposableBLSupport.bOneTwo n m
  | .dipole i => (DipoleFlavorSelection.selector DgtFlavorRestriction.leptonIR
      DgtFlavorRestriction.leptonIR DgtFlavorRestriction.mu
      (DgtFlavorRestriction.targetCovector i)).range

instance (t : DgtTarget) : Zero (dgtDomain t) := by
  cases t <;> unfold dgtDomain <;> infer_instance

def dgtRequest : Request DgtTarget where
  forbid := {t | t = .baryon}
  allow := {t | ∃ i, t = .dipole i}

theorem dgt_satisfies : Satisfies dgtDomain dgtRequest := by
  constructor
  · intro t ht; change t = .baryon at ht; subst t
    intro f; funext n m
    exact DgtFlavorRestriction.all_bnv_forbidden n m (f n m)
  · intro t ht
    obtain ⟨i,rfl⟩ := ht
    exact MixedSelectionPatterns.dgt_selector_range_allowed i

theorem dgt_components : Forbidden (dgtDomain .baryon) ∧
    (∀ i : Fin 2, Allowed (dgtDomain (.dipole i))) :=
  ⟨forbidden dgtDomain dgtRequest dgt_satisfies .baryon rfl,
   fun i => allowed dgtDomain dgtRequest dgt_satisfies (.dipole i) ⟨i,rfl⟩⟩

/-- Switching from IR to UV removes allowance of these prescribed outputs. -/
theorem dgt_uv_not_allowed (i : Fin 2) : ¬ Allowed
    (DipoleFlavorSelection.selector DgtFlavorRestriction.leptonUV
      DgtFlavorRestriction.leptonUV DgtFlavorRestriction.mu
      (DgtFlavorRestriction.targetCovector i)).range := by
  apply (forbidden_iff_not_allowed _).mp
  apply (range_forbidden_iff _).mpr
  apply LinearMap.ext
  intro c
  exact congrFun (LinearMap.congr_fun DgtFlavorRestriction.uv_dipoles_forbidden c) i

inductive QuarticityTarget where
  | smLTwo | bare | dressed
  deriving DecidableEq

/-- SM/Higgs all-degree L2, bare nuR pair, and eta-dressed nuR pair are distinct domains. -/
def quarticityDomain : QuarticityTarget → Type
  | .smLTwo => ∀ n m : ℕ, ComposableBLSupport.Input
      QuarticityAdapters.smFlavor QuarticityAdapters.smScalar
      (fun q => q.2.natAbs = 2) n m
  | .bare => QuarticityAdapters.Bare
  | .dressed => QuarticityAdapters.Dressed

instance (t : QuarticityTarget) : Zero (quarticityDomain t) := by
  cases t <;> unfold quarticityDomain <;> infer_instance

def quarticityRequest : Request QuarticityTarget where
  forbid := {t | t = .smLTwo ∨ t = .bare}
  allow := {t | t = .dressed}

theorem quarticity_satisfies : Satisfies quarticityDomain quarticityRequest := by
  constructor
  · intro t ht
    rcases ht with rfl | rfl
    · intro f; funext n m
      exact QuarticityAdapters.sm_lTwo_forbidden n m (f n m)
    · exact QuarticityAdapters.bare_forbidden
  · intro t ht; change t = .dressed at ht; subst t
    exact QuarticityAdapters.exists_dressed

theorem quarticity_components : Forbidden (quarticityDomain .smLTwo) ∧
    Forbidden (quarticityDomain .bare) ∧ Allowed (quarticityDomain .dressed) :=
  ⟨forbidden quarticityDomain quarticityRequest quarticity_satisfies .smLTwo (Or.inl rfl),
   forbidden quarticityDomain quarticityRequest quarticity_satisfies .bare (Or.inr rfl),
   allowed quarticityDomain quarticityRequest quarticity_satisfies .dressed rfl⟩

/-- The existing dressed witness prevents extending prohibition to that domain. -/
theorem quarticity_dressed_not_forbidden : ¬ Forbidden (quarticityDomain .dressed) := by
  intro h
  exact (forbidden_iff_not_allowed _).mp h quarticity_components.2.2

def forbidDressed : Request QuarticityTarget := ⟨{t | t = .dressed}, ∅⟩

theorem quarticity_extended_request_inconsistent :
    ¬ Satisfies quarticityDomain (combine quarticityRequest forbidDressed) :=
  conflict quarticityDomain _ .dressed (Or.inr rfl) (Or.inl rfl)
end
end Physics.DgtQuarticityMixedRequests
