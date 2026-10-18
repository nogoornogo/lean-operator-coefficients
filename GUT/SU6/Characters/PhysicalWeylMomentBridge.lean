import GUT.SU6.Characters.PhysicalTorusCharacterBridge

/-!
# The fifth-moment obstruction from a dual chiral index

Equality of antisymmetrized characters suffices for hypercharge character rigidity: duality negates an
odd moment, so the dual difference doubles the fifth moment. No recovery of
self-dual sectors or of the full light spectrum is used. The function-level
bridge applies to actual continuous-unitary SU(6) sources on any integral
physical cocharacter pair.
-/

set_option autoImplicit false

namespace GUT.PhysicalWeylMomentBridge

noncomputable section

open PhysicalFifthMomentBridge

def dual {W : Type*} [Neg W] (p : W →₀ ℤ) : W →₀ ℤ :=
  Finsupp.mapDomain Neg.neg p

def chiralDifference {W : Type*} [Neg W] (p : W →₀ ℤ) : W →₀ ℤ := p - dual p

theorem mapDomain_dual {W U : Type*} [Neg W] [Neg U]
    (f : W → U) (hf : ∀ w, f (-w) = -f w) (p : W →₀ ℤ) :
    Finsupp.mapDomain f (dual p) = dual (Finsupp.mapDomain f p) := by
  unfold dual
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1
  funext w
  exact hf w

theorem mapDomain_chiralDifference {W U : Type*} [Neg W] [Neg U]
    (f : W → U) (hf : ∀ w, f (-w) = -f w) (p : W →₀ ℤ) :
    Finsupp.mapDomain f (chiralDifference p) =
      chiralDifference (Finsupp.mapDomain f p) := by
  simp only [chiralDifference, Finsupp.mapDomain_sub, mapDomain_dual f hf]

def fifthMomentAddHom (a b t h : ℚ) : PhysicalCharacter →+ ℚ where
  toFun p := fifthMomentValue p a b t h
  map_zero' := fifthMomentValue_zero a b t h
  map_add' p q := fifthMomentValue_add p q a b t h

theorem fifthMomentValue_dual (p : PhysicalCharacter) (a b t h : ℚ) :
    fifthMomentValue (dual p) a b t h = -fifthMomentValue p a b t h := by
  unfold fifthMomentValue dual
  rw [Finsupp.sum_mapDomain_index]
  · rw [← Finsupp.sum_neg]
    apply Finsupp.sum_congr
    intro w _
    have he : (-w).eval a b t h = -w.eval a b t h := by
      simp only [PhysicalWeight.eval, Pi.neg_apply]
      ring
    rw [he]
    ring
  · simp
  · intros; push_cast; ring

theorem fifthMomentValue_chiralDifference (p : PhysicalCharacter) (a b t h : ℚ) :
    fifthMomentValue (chiralDifference p) a b t h = 2 * fifthMomentValue p a b t h := by
  change fifthMomentAddHom a b t h (p - dual p) = _
  rw [map_sub]
  change fifthMomentValue p a b t h - fifthMomentValue (dual p) a b t h = _
  rw [fifthMomentValue_dual]
  ring

def IsDualSMRestriction (p : AmbientWeightLattice.Character)
    (generations singlets : ℤ) (m n : ℚ) : Prop :=
  chiralDifference (restrictCharacter m n p) =
    chiralDifference (PhysicalFifthMomentBridge.zscale generations smCharacter +
      singletCharacter singlets)

theorem hasSMFifthMoment_of_dualRestriction (p : AmbientWeightLattice.Character)
    (generations singlets : ℤ) (m n : ℚ)
    (ht : IsDualSMRestriction p generations singlets m n) :
    AmbientCharacterBridge.HasSMFifthMoment (generations : ℚ) m n p := by
  intro a b t h
  have he := congrArg (fun q => fifthMomentValue q a b t h) ht
  simp only [fifthMomentValue_chiralDifference, fifthMomentValue_add,
    fifthMomentValue_zscale, fifthMomentValue_smCharacter,
    fifthMomentValue_singletCharacter, add_zero] at he
  rw [← fifthMomentValue_restrictCharacter]
  linarith

theorem eq_standard_of_virtualModel_dualRestriction
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    (generations singlets : ℤ) (m n : ℚ) (hn : generations ≠ 0)
    (ht : IsDualSMRestriction M.poly generations singlets m n) :
    m = -2 ∧ n = 3 := by
  apply AmbientCharacterBridge.eq_standard_of_virtualModel_fifthMoment
    M (generations : ℚ) m n
  · exact_mod_cast hn
  · exact hasSMFifthMoment_of_dualRestriction M.poly generations singlets m n ht

open PhysicalTorusCharacterBridge

def evalAddHom (x : UnitAddTorus (Fin 4)) : IntegralPhysicalCharacter →+ ℂ where
  toFun p := eval p x
  map_zero' := by simp [eval]
  map_add' p q := by
    unfold eval
    rw [Finsupp.sum_add_index]
    · simp
    · intros; push_cast; ring

theorem eval_dual (p : IntegralPhysicalCharacter) (x : UnitAddTorus (Fin 4)) :
    eval (dual p) x = eval p (-x) := by
  unfold eval dual
  rw [Finsupp.sum_mapDomain_index]
  · apply Finsupp.sum_congr
    intro w _
    congr 1
    simp [UnitAddTorus.mFourier, neg_smul]
  · simp
  · intros; push_cast; ring

theorem eval_chiralDifference (p : IntegralPhysicalCharacter) (x : UnitAddTorus (Fin 4)) :
    eval (chiralDifference p) x = eval p x - eval p (-x) := by
  change evalAddHom x (p - dual p) = _
  rw [map_sub]
  exact congrArg (fun z => eval p x - z) (eval_dual p x)

theorem toRationalCharacter_chiralDifference (p : IntegralPhysicalCharacter) :
    toRationalCharacter (chiralDifference p) = chiralDifference (toRationalCharacter p) :=
  mapDomain_chiralDifference exponentWeight (fun w => by ext i; simp [exponentWeight]) p

def IsDualSMCharacterOnPhysicalTorus
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (generations singlets m n : ℤ) : Prop :=
  ∀ x : UnitAddTorus (Fin 4),
    AmbientCharacterBridge.finiteVirtualRestrictedCharacter chi (physicalDiagonalPoint m n x) -
      AmbientCharacterBridge.finiteVirtualRestrictedCharacter chi (physicalDiagonalPoint m n (-x)) =
    eval (exactSMCharacter generations singlets) x -
      eval (exactSMCharacter generations singlets) (-x)

theorem dualRestriction_of_characterOnPhysicalTorus
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    (generations singlets m n : ℤ)
    (ht : IsDualSMCharacterOnPhysicalTorus (chi := chi) generations singlets m n) :
    IsDualSMRestriction M.poly generations singlets (m : ℚ) (n : ℚ) := by
  have hi : chiralDifference (restrictIntegralCharacter m n M.poly) =
      chiralDifference (exactSMCharacter generations singlets) := by
    apply Fourier.eval_faithful
    intro x
    rw [eval_chiralDifference, eval_chiralDifference]
    simp only [eval_restrictIntegralCharacter_eq_diagonalEval, M.evaluates_character]
    exact ht x
  have hr := congrArg toRationalCharacter hi
  simpa only [IsDualSMRestriction, toRationalCharacter_chiralDifference, toRationalCharacter_restrictIntegralCharacter,
    toRationalCharacter_exactSMCharacter] using hr

theorem eq_standard_of_virtualModel_dualCharacterOnPhysicalTorus
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    (generations singlets m n : ℤ) (hn : generations ≠ 0)
    (ht : IsDualSMCharacterOnPhysicalTorus (chi := chi) generations singlets m n) :
    m = -2 ∧ n = 3 := by
  have he := eq_standard_of_virtualModel_dualRestriction M generations singlets
    (m : ℚ) (n : ℚ) hn (dualRestriction_of_characterOnPhysicalTorus M generations singlets m n ht)
  exact ⟨by exact_mod_cast he.1, by exact_mod_cast he.2⟩

theorem eq_standard_of_continuousUnitarySource_dualCharacterOnPhysicalTorus
    {A : Type*} (source : StandardPhysicalSource.FiniteChargedContinuousUnitarySource A)
    (generations singlets m n : ℤ) (hn : generations ≠ 0)
    (ht : IsDualSMCharacterOnPhysicalTorus (chi := source.toVirtual) generations singlets m n) :
    m = -2 ∧ n = 3 :=
  eq_standard_of_virtualModel_dualCharacterOnPhysicalTorus source.ambientLaurentModel
    generations singlets m n hn ht

end

end GUT.PhysicalWeylMomentBridge
