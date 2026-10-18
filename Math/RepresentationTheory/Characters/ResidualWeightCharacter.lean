import Math.RepresentationTheory.Characters.ResidualWeightSpace

/-!
# Faithful finite torus characters with residual character coefficients

H need not be Abelian. For each h the coefficient at chi is the trace of h
on the actual chi-weight space. Dual traces reverse both the torus weight
and the residual element; no Hilbert structure on an algebraic dual is assumed.
-/

set_option autoImplicit false

namespace Math.ResidualWeightCharacter

noncomputable section

open scoped BigOperators
open ResidualWeightSpace

variable {T : Type*} [CommGroup T]

abbrev Polynomial := (T →* Circle) →₀ ℂ

def eval (p : Polynomial (T := T)) (t : T) : ℂ :=
  p.sum fun chi z => z * (chi t : ℂ)

theorem eval_injective (p q : Polynomial (T := T))
    (he : ∀ t, eval p t = eval q t) : p = q := by
  have hi : LinearIndependent ℂ (fun chi : T →* Circle => fun t => (chi t : ℂ)) :=
    (linearIndependent_monoidHom T ℂ).comp
    UnitaryCharacterSpectrum.complexCharacter
    UnitaryCharacterSpectrum.complexCharacter_injective
  apply hi.finsuppLinearCombination_injective
  ext t
  simpa [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, eval] using he t

def dual (p : Polynomial (T := T)) : Polynomial (T := T) :=
  Finsupp.mapDomain (fun chi => chi⁻¹) p

@[simp] theorem dual_apply (p : Polynomial (T := T)) (chi : T →* Circle) :
    dual p chi = p chi⁻¹ := by
  simpa [dual] using Finsupp.mapDomain_apply_of_injective inv_injective p chi⁻¹

theorem eval_dual (p : Polynomial (T := T)) (t : T) :
    eval (dual p) t = eval p t⁻¹ := by
  unfold dual eval
  rw [Finsupp.sum_mapDomain_index]
  · simp
  · simp
  · intros; simp [add_mul]

@[simp] theorem eval_sub (p q : Polynomial (T := T)) (t : T) :
    eval (p - q) t = eval p t - eval q t := by
  simp [eval, Finsupp.sum_sub_index, sub_mul]

theorem coeff_comp_eq_of_eval_invariant (p : Polynomial (T := T)) (a : T ≃* T)
    (he : ∀ t, eval p (a t) = eval p t) (chi : T →* Circle) :
    p (chi.comp a.toMonoidHom) = p chi := by
  let f : (T →* Circle) → (T →* Circle) := fun psi => psi.comp a.toMonoidHom
  have hi : Function.Injective f := by
    intro psi phi h
    apply MonoidHom.ext
    intro t
    simpa [f] using congrArg (fun c : T →* Circle => c (a.symm t)) h
  have hp : Finsupp.mapDomain f p = p := by
    apply eval_injective
    intro t
    unfold eval
    rw [Finsupp.sum_mapDomain_index]
    · exact he t
    · simp
    · intros; simp [add_mul]
  have hc := congrArg (fun q : Polynomial (T := T) => q (f chi)) hp
  rw [Finsupp.mapDomain_apply_of_injective hi] at hc
  exact hc.symm

variable {H E : Type*} [Group H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ (T × H) E)
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation (torus rho))

def coefficients (h : H) : Polynomial (T := T) :=
  letI := UnitaryCharacterProfile.activeFintype (torus rho) hu
  ∑ chi : UnitaryCharacterProfile.Active (torus rho),
    Finsupp.single chi.val ((representation rho chi.val).character h)

@[simp] theorem coefficients_apply (h : H) (chi : T →* Circle) :
    coefficients rho hu h chi = (representation rho chi).character h := by
  classical
  let := UnitaryCharacterProfile.activeFintype (torus rho) hu
  unfold coefficients
  rw [Finsupp.finsetSum_apply]
  by_cases hc : space rho chi = ⊥
  · have hz : (representation rho chi).character h = 0 := by
      let : Subsingleton (space rho chi) := by rw [hc]; infer_instance
      have hm : representation rho chi h = 0 := Subsingleton.elim _ _
      simp [Representation.character, hm]
    rw [hz]
    apply Finset.sum_eq_zero
    intro psi _
    apply Finsupp.single_eq_of_ne
    intro he
    exact psi.property (he ▸ hc)
  · rw [Finset.sum_eq_single (⟨chi, hc⟩ : UnitaryCharacterProfile.Active (torus rho))]
    · simp
    · intro psi _ hne
      apply Finsupp.single_eq_of_ne
      intro he
      exact hne (Subtype.ext he.symm)
    · simp

theorem eval_coefficients (t : T) (h : H) :
    eval (coefficients rho hu h) t = rho.character (t, h) := by
  classical
  let := UnitaryCharacterProfile.activeFintype (torus rho) hu
  rw [character_expansion rho hu]
  unfold coefficients eval
  rw [← Finsupp.sum_finsetSum_index]
  · simp [mul_comm]
  · intros; simp
  · intros; simp [add_mul]

def dualCoefficients (h : H) : Polynomial (T := T) :=
  coefficients rho hu h - dual (coefficients rho hu h⁻¹)

/-- The actual residual representation is dualized at the opposite weight. -/
def index (chi : T →* Circle) (h : H) : ℂ :=
  (representation rho chi).character h - (representation rho chi⁻¹).dual.character h

@[simp] theorem dualCoefficients_apply (h : H) (chi : T →* Circle) :
    dualCoefficients rho hu h chi = index rho chi h := by
  simp [dualCoefficients, index, Representation.char_dual]

theorem eval_dualCoefficients (t : T) (h : H) :
    eval (dualCoefficients rho hu h) t = rho.character (t, h) - rho.dual.character (t, h) := by
  simp [dualCoefficients, eval_dual, eval_coefficients, Representation.char_dual]

include hu in
/-- Only full dual traces are assumed invariant; individual weight spaces
need not be carried into each other by an action on the light radical. -/
theorem index_invariant (a : T ≃* T)
    (he : ∀ t h, rho.character (a t, h) - rho.dual.character (a t, h) =
      rho.character (t, h) - rho.dual.character (t, h))
    (chi : T →* Circle) (h : H) :
    index rho (chi.comp a.toMonoidHom) h = index rho chi h := by
  have hc := coeff_comp_eq_of_eval_invariant (dualCoefficients rho hu h) a
    (fun t => by simpa [eval_dualCoefficients] using he t h) chi
  simpa using hc

end
end Math.ResidualWeightCharacter
