import Math.Algebra.Jets.JetCombined
import Math.RepresentationTheory.Jets.JetFunctor
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! A constant-coefficient scalar equation and all its derivative descendants.
The free algebra on the quotient generators is compared with the actual EOM ideal. -/
namespace Math.JetEquation
set_option autoImplicit false
noncomputable section
open JetLinear JetDirections MvPolynomial

variable {S I : Type*} (q : Symbols I)

def generators (S : Type*) (q : Symbols I) : Set (Jet S I) :=
  {v | ∃ s p, ofSymbols s (p * q) = v}

def relations (S : Type*) (q : Symbols I) : Submodule ℂ (Jet S I) :=
  Submodule.span ℂ (generators S q)

theorem descendant_mem (s : S) (p : Symbols I) : ofSymbols s (p * q) ∈ relations S q :=
  Submodule.subset_span ⟨s, p, rfl⟩

theorem shift_stable (i : I) : relations S q ≤ (relations S q).comap (JetLinear.shift i) := by
  apply Submodule.span_le.mpr
  rintro v ⟨s, p, rfl⟩
  change JetLinear.shift i (ofSymbols s (p * q)) ∈ relations S q
  rw [shift_ofSymbols, show p * q * X i = (p * X i) * q by ring]
  exact descendant_mem q s (p * X i)

abbrev Generator (S : Type*) (q : Symbols I) := Jet S I ⧸ relations S q

def shift (i : I) : Generator S q →ₗ[ℂ] Generator S q :=
  Submodule.mapQ _ _ (JetLinear.shift i) (shift_stable q i)

@[simp] theorem shift_mk (i : I) (v : Jet S I) :
    shift q i ((relations S q).mkQ v) = (relations S q).mkQ (JetLinear.shift i v) := rfl

theorem shift_commute (i j : I) :
    (shift (S := S) q i).comp (shift q j) = (shift q j).comp (shift q i) := by
  apply LinearMap.ext
  intro v
  obtain ⟨v, rfl⟩ := (relations S q).mkQ_surjective v
  simp only [LinearMap.comp_apply, shift_mk]
  exact congrArg (relations S q).mkQ (LinearMap.congr_fun (JetLinear.shift_commute i j) v)

theorem internal_stable (f : JetLinear.Field S →ₗ[ℂ] JetLinear.Field S) :
    relations S q ≤ (relations S q).comap (JetLinear.map f) := by
  apply Submodule.span_le.mpr
  rintro v ⟨s, p, rfl⟩
  change JetLinear.map f (ofSymbols s (p * q)) ∈ relations S q
  rw [internal_ofSymbols]
  induction f (Finsupp.single s 1) using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simpa only [map_add] using (relations S q).add_mem hv hw
  | single t c => rw [attach_single]; exact (relations S q).smul_mem c (descendant_mem q t p)

theorem direction_stable (f : Direction I →ₗ[ℂ] Direction I) (hq : symbolMap f q = q) :
    relations S q ≤ (relations S q).comap (jetMap f) := by
  apply Submodule.span_le.mpr
  rintro v ⟨s, p, rfl⟩
  change jetMap f (ofSymbols s (p * q)) ∈ relations S q
  simp only [jetMap, lift_ofSymbols, AlgHom.toLinearMap_apply, map_mul, hq]
  exact descendant_mem q s (symbolMap f p)

theorem combined_stable {H : Type*} [Monoid H]
    (ρ : Representation ℂ H (JetLinear.Field S)) (σ : Representation ℂ H (Direction I))
    (hq : ∀ h, symbolMap (σ h) q = q) (h : H) :
    relations S q ≤ (relations S q).comap (combined ρ σ h) :=
  fun _ hp => internal_stable q (ρ h) (direction_stable q (σ h) (hq h) hp)

def generatorAction {H : Type*} [Monoid H]
    (ρ : Representation ℂ H (JetLinear.Field S)) (σ : Representation ℂ H (Direction I))
    (hq : ∀ h, symbolMap (σ h) q = q) : Representation ℂ H (Generator S q) :=
  (combined ρ σ).quotient (relations S q) (combined_stable q ρ σ hq)

theorem generator_covariant [Fintype I] {H : Type*} [Monoid H]
    (ρ : Representation ℂ H (JetLinear.Field S)) (σ : Representation ℂ H (Direction I))
    (hq : ∀ h, symbolMap (σ h) q = q) (h : H) (i : I) (v : Generator S q) :
    generatorAction q ρ σ hq h (shift q i v) =
      ∑ j, (σ h (Finsupp.single i 1)) j • shift q j (generatorAction q ρ σ hq h v) := by
  obtain ⟨v, rfl⟩ := (relations S q).mkQ_surjective v
  change (relations S q).mkQ (combined ρ σ h (JetLinear.shift i v)) = _
  rw [combined_covariant, map_sum]
  simp only [map_smul]
  rfl

abbrev Algebra (S : Type*) (q : Symbols I) := SymmetricAlgebra ℂ (Generator S q)

def derivative (i : I) : Algebra S q →ₗ[ℂ] Algebra S q :=
  PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear (shift q i)

theorem derivative_mul (i : I) (p r : Algebra S q) :
    derivative q i (p * r) = derivative q i p * r + p * derivative q i r :=
  PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear_mul _ _ _

theorem derivative_commute (i j : I) (p : Algebra S q) :
    derivative q i (derivative q j p) = derivative q j (derivative q i p) :=
  PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear_comm_apply (shift_commute q i j) p

def projection : ScalarJetAlgebra.Algebra S I →ₐ[ℂ] Algebra S q :=
  aeval (fun j => SymmetricAlgebra.ι ℂ (Generator S q) ((relations S q).mkQ (Finsupp.single j 1)))

@[simp] theorem projection_X (j : ScalarJetAlgebra.Index S I) :
    projection q (X j) = SymmetricAlgebra.ι ℂ (Generator S q)
      ((relations S q).mkQ (Finsupp.single j 1)) := by simp [projection]

theorem projection_linearForm (v : Jet S I) :
    projection q (JetLinear.linearForm v) =
      SymmetricAlgebra.ι ℂ (Generator S q) ((relations S q).mkQ v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c =>
    simp only [show Finsupp.single j c = c • Finsupp.single j (1 : ℂ) by simp,
      map_smul, JetLinear.linearForm, Finsupp.linearCombination_single, one_smul, projection_X]

theorem projection_derivative (i : I) (p : ScalarJetAlgebra.Algebra S I) :
    projection q (ScalarJetAlgebra.totalDerivative i p) = derivative q i (projection q p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [projection, derivative]
  | add p r hp hr => simp only [map_add, hp, hr]
  | mul_X p j hp =>
    simp only [ScalarJetAlgebra.totalDerivative_mul, map_add, map_mul, hp,
      ScalarJetAlgebra.totalDerivative_X, projection_X, derivative_mul]
    simp only [derivative, PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear_ι, shift_mk,
      JetLinear.shift_single]
    ring

def ideal (S : Type*) (q : Symbols I) : Ideal (ScalarJetAlgebra.Algebra S I) :=
  Ideal.span (Set.range (fun v : relations S q => JetLinear.linearForm v.val))

theorem ideal_le_ker : ideal S q ≤ RingHom.ker (projection (S := S) q).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨v, rfl⟩
  change projection q (JetLinear.linearForm v.val) = 0
  rw [projection_linearForm, show (relations S q).mkQ v.val = 0 from
    (Submodule.Quotient.mk_eq_zero _).mpr v.property, map_zero]

abbrev PolynomialQuotient (S : Type*) (q : Symbols I) := ScalarJetAlgebra.Algebra S I ⧸ ideal S q

def toFree : PolynomialQuotient S q →ₐ[ℂ] Algebra S q :=
  Ideal.Quotient.liftₐ (ideal S q) (projection q) (ideal_le_ker q)

@[simp] theorem toFree_mk (p : ScalarJetAlgebra.Algebra S I) :
    toFree q (Ideal.Quotient.mk (ideal S q) p) = projection q p :=
  Ideal.Quotient.liftₐ_apply _ _ _ _

def quotientGenerator : Generator S q →ₗ[ℂ] PolynomialQuotient S q :=
  (relations S q).liftQ
    ((Ideal.Quotient.mkₐ ℂ (ideal S q)).toLinearMap.comp JetLinear.linearForm) (by
      intro v hv
      change Ideal.Quotient.mk _ (JetLinear.linearForm v) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.subset_span ⟨⟨v, hv⟩, rfl⟩)

def fromFree : Algebra S q →ₐ[ℂ] PolynomialQuotient S q := SymmetricAlgebra.lift (quotientGenerator q)

@[simp] theorem fromFree_generator (v : Jet S I) :
    fromFree q (SymmetricAlgebra.ι ℂ (Generator S q) ((relations S q).mkQ v)) =
      Ideal.Quotient.mk (ideal S q) (JetLinear.linearForm v) := by
  rw [fromFree, SymmetricAlgebra.lift_ι_apply]
  rfl

theorem fromFree_projection (p : ScalarJetAlgebra.Algebra S I) :
    fromFree q (projection q p) = Ideal.Quotient.mkₐ ℂ (ideal S q) p := by
  have h : (fromFree (S := S) q).comp (projection q) = Ideal.Quotient.mkₐ ℂ (ideal S q) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [fromFree, projection_X, quotientGenerator, JetLinear.linearForm]
  exact DFunLike.congr_fun h p

def presentationEquiv : PolynomialQuotient S q ≃ₐ[ℂ] Algebra S q where
  toFun := toFree q
  invFun := fromFree q
  left_inv p := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
    exact fromFree_projection q p
  right_inv p := by
    have h : (toFree (S := S) q).comp (fromFree q) = AlgHom.id ℂ _ := by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro v
      obtain ⟨v, rfl⟩ := (relations S q).mkQ_surjective v
      change toFree q (fromFree q (SymmetricAlgebra.ι ℂ (Generator S q)
        ((relations S q).mkQ v))) = SymmetricAlgebra.ι ℂ (Generator S q) ((relations S q).mkQ v)
      rw [fromFree_generator, toFree_mk, projection_linearForm]
    exact DFunLike.congr_fun h p
  map_mul' := map_mul (toFree q)
  map_add' := map_add (toFree q)
  commutes' := AlgHom.commutes (toFree q)

theorem projection_surjective : Function.Surjective (projection (S := S) q) := by
  intro p
  obtain ⟨a, ha⟩ := (presentationEquiv (S := S) q).surjective p
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨p, ha⟩

theorem projection_ker : RingHom.ker (projection (S := S) q).toRingHom = ideal S q := by
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change projection q p = 0 at hp
    have h := congrArg (fromFree q) hp
    simpa only [fromFree_projection, map_zero, Ideal.Quotient.mkₐ_eq_mk] using h
  · exact ideal_le_ker q

end
end Math.JetEquation
