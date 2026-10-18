import GUT.SU6.SelectionRules.Models.PhysicalWeylMassSource

open Math

/-! Scalar residual actions and the trace of their full character refinement. -/

set_option autoImplicit false

namespace GUT.ScalarResidualSource

noncomputable section

open ContinuousUnitaryWeightDecomposition FiniteAbelianChargeSectors
open FiniteSemisimpleDecomposition StandardBlockGaugeCancellation
open StandardPhysicalSource PhysicalChargeResolvedBridge PhysicalChargedCharacterBridge
open PhysicalRestrictionBridge

variable {H : Type*} [CommGroup H]

def action (R : ContinuousUnitarySU6Representation) (chi : H →* Circle) :
    CommutingAction H R where
  rho :=
    { toFun h := LinearMap.lsmul ℂ R.V (chi h : ℂ)
      map_one' := by ext v; simp
      map_mul' h k := by
        ext v
        change (chi (h * k) : ℂ) • v = (chi h : ℂ) • ((chi k : ℂ) • v)
        rw [map_mul, Circle.coe_mul, mul_smul] }
  unitary := by
    intro h v w
    change inner ℂ ((chi h : ℂ) • v) ((chi h : ℂ) • w) = _
    rw [inner_smul_left, inner_smul_right, ← Circle.coe_inv_eq_conj]
    simp
  commutes := by intro h g; ext v; simp

theorem blockCharacter_eq_of_scalar {R : ContinuousUnitarySU6Representation}
    (S : CommutingAction H R) (chi : H →* Circle)
    (hS : ∀ h v, S.rho h v = (chi h : ℂ) • v)
    (D : Decomposition S.rho) (i : Fin D.numberOfBlocks) :
    S.blockCharacter D i = chi := by
  let : IsSimpleModule (MonoidAlgebra ℂ H) (D.block i) := D.simple i
  let : Nontrivial (D.block i) := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) (D.block i)
  ext h
  apply FaithfulSMul.eq_of_smul_eq_smul (α := D.block i)
  intro v
  rw [← S.blockRepresentation_action_eq_character D i h v]
  apply (D.blockAmbientEquiv i).injective
  change (D.blockAmbientEquiv i).toIntertwiningMap (D.blockRepresentation i h v) = _
  rw [Representation.IntertwiningMap.isIntertwining, map_smul]
  exact Subtype.ext (hS h _)

theorem chargedSectorSource_uniform {R : ContinuousUnitarySU6Representation}
    (S : CommutingAction H R) (chi : H →* Circle)
    (hS : ∀ h v, S.rho h v = (chi h : ℂ) • v)
    (D : Decomposition S.rho) (c : ℤ) :
    ∀ s ∈ S.chargedSectorSource D c, s.offset = Additive.ofMul chi := by
  intro s hs
  simp only [CommutingAction.chargedSectorSource, List.mem_ofFn] at hs
  obtain ⟨i, rfl⟩ := hs
  apply Additive.toMul.injective
  change S.indexedCharacter D i = chi
  have hi := (S.activeCharacterEquiv D i).property
  simp only [CommutingAction.activeCharacters, Finset.mem_image] at hi
  obtain ⟨j, _, hj⟩ := hi
  exact hj.symm.trans (blockCharacter_eq_of_scalar S chi hS D j)

theorem ordinaryChargedSource_uniform (matter : OrdinaryAbelianSource H)
    (chi : H →* Circle)
    (hS : ∀ s ∈ matter, ∀ h v, s.action.rho h v = (chi h : ℂ) • v) :
    ∀ s ∈ ordinaryChargedSource matter, s.offset = Additive.ofMul chi := by
  induction matter with
  | nil => simp [ordinaryChargedSource, OrdinaryAbelianSource.toCommonGaugeSource,
      CommonGaugeSource.toChargedSource]
  | cons s matter ih =>
    intro t ht
    change t ∈ s.toCommonGaugeSummand.toChargedSource ++ ordinaryChargedSource matter at ht
    rcases List.mem_append.mp ht with ht | ht
    · apply chargedSectorSource_uniform _ chi _ _ _ t ht
      intro h v
      change s.toCommonGaugeSummand.twisted.externalRepresentation h v = _
      rw [OrdinaryAbelianSummand.toCommonGaugeSummand_externalRepresentation]
      exact hS s (by simp) h v
    · exact ih (fun u hu => hS u (List.mem_cons_of_mem s hu)) t ht

theorem source_character_uniform (m n : ℤ)
    (source : FiniteChargedContinuousUnitarySource (FiniteAbelianChargeSectors.ChargeLabel H))
    (chi : H →* Circle)
    (hu : ∀ s ∈ source, s.offset = Additive.ofMul chi)
    (x : UnitAddTorus (Fin 4)) (h : H) :
    FiniteVirtualGroupRepresentation.character (sourceProductRepresentation m n source)
        (Multiplicative.ofAdd x, h) =
      (chi h : ℂ) * AmbientCharacterBridge.finiteVirtualRestrictedCharacter source.toVirtual
        (PhysicalTorusCharacterBridge.physicalDiagonalPoint m n x) := by
  induction source with
  | nil => change (0 : ℂ) = _ * 0; exact (mul_zero _).symm
  | cons s source ih =>
    have hs := hu s (by simp)
    have hrho : chargedPhysicalRho m n s (Multiplicative.ofAdd x, h) =
        (chi h : ℂ) • s.rep.rho (PhysicalSMTorusTarget.embedding m n (Multiplicative.ofAdd x)) := by
      ext v
      simp [chargedPhysicalRho, hs]
    have htrace : (chargedPhysicalRho m n s).character (Multiplicative.ofAdd x, h) =
        (chi h : ℂ) * s.rep.rho.character
          (PhysicalSMTorusTarget.embedding m n (Multiplicative.ofAdd x)) := by
      change LinearMap.trace ℂ s.rep.V _ = _
      rw [hrho, map_smul]
      rfl
    change (s.coeff : ℂ) * (chargedPhysicalRho m n s).character _ + _ =
      (chi h : ℂ) * ((s.coeff : ℂ) * s.rep.rho.character _ + _)
    rw [htrace, ih (fun t ht => hu t (List.mem_cons_of_mem s ht)),
      PhysicalSMTorusTarget.embedding_ofAdd]
    simp only [FiniteChargedContinuousUnitarySource.toVirtual]
    ring

theorem fields_character_uniform (m n : ℤ) (matter : OrdinaryAbelianSource H)
    (hc : ∀ s ∈ matter, 0 ≤ s.coeff) (chi : H →* Circle)
    (hu : ∀ s ∈ matter, ∀ h v, s.action.rho h v = (chi h : ℂ) • v)
    (x : UnitAddTorus (Fin 4)) (h : H) :
    (PhysicalMassSpectrumBridge.ordinaryPositiveRepresentation m n matter).rho.character
        (Multiplicative.ofAdd x, h) =
      (chi h : ℂ) * AmbientCharacterBridge.finiteVirtualRestrictedCharacter
        matter.toFiniteVirtual (PhysicalTorusCharacterBridge.physicalDiagonalPoint m n x) := by
  rw [PhysicalWeylMassSource.fields_character m n matter hc, ordinaryPhysicalResolvedCharacter,
    ← sourceProductRepresentation_character,
    source_character_uniform m n _ chi (ordinaryChargedSource_uniform matter chi hu),
    ordinaryChargedSource_restrictedCharacter_eq]

theorem ordinaryChargedSource_append (S T : OrdinaryAbelianSource H) :
    ordinaryChargedSource (S ++ T) = ordinaryChargedSource S ++ ordinaryChargedSource T := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    change s.toCommonGaugeSummand.toChargedSource ++ ordinaryChargedSource (S ++ T) =
      (s.toCommonGaugeSummand.toChargedSource ++ ordinaryChargedSource S) ++ _
    rw [ih, List.append_assoc]

theorem source_character_append (m n : ℤ)
    (S T : FiniteChargedContinuousUnitarySource (FiniteAbelianChargeSectors.ChargeLabel H))
    (g : StandardSMCharacterTarget.CombinedGroup H) :
    (sourceProductRepresentation m n (S ++ T)).character g =
      (sourceProductRepresentation m n S).character g +
        (sourceProductRepresentation m n T).character g := by
  induction S with
  | nil => exact (zero_add _).symm
  | cons s S ih =>
    change (s.coeff : ℂ) * (chargedPhysicalRho m n s).character g + _ =
      ((s.coeff : ℂ) * (chargedPhysicalRho m n s).character g + _) + _
    exact (congrArg (fun z : ℂ => (s.coeff : ℂ) *
      (chargedPhysicalRho m n s).character g + z) ih).trans (add_assoc _ _ _).symm

theorem fields_character_append (m n : ℤ) (S T : OrdinaryAbelianSource H)
    (hS : ∀ s ∈ S, 0 ≤ s.coeff) (hT : ∀ s ∈ T, 0 ≤ s.coeff)
    (x : UnitAddTorus (Fin 4)) (h : H) :
    (PhysicalMassSpectrumBridge.ordinaryPositiveRepresentation m n (S ++ T)).rho.character
        (Multiplicative.ofAdd x, h) =
      (PhysicalMassSpectrumBridge.ordinaryPositiveRepresentation m n S).rho.character
        (Multiplicative.ofAdd x, h) +
      (PhysicalMassSpectrumBridge.ordinaryPositiveRepresentation m n T).rho.character
        (Multiplicative.ofAdd x, h) := by
  have hST : ∀ s ∈ S ++ T, 0 ≤ s.coeff := by
    intro s hs
    exact (List.mem_append.mp hs).elim (hS s) (hT s)
  rw [PhysicalWeylMassSource.fields_character m n _ hST,
    PhysicalWeylMassSource.fields_character m n _ hS,
    PhysicalWeylMassSource.fields_character m n _ hT]
  simp only [ordinaryPhysicalResolvedCharacter, ← sourceProductRepresentation_character]
  rw [ordinaryChargedSource_append, source_character_append]

end

end GUT.ScalarResidualSource
