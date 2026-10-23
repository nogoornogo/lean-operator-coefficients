import Math.Algebra.Jets.JetEquation

/-! Component-mixing linear constant-coefficient equations, with all ordinary
derivative descendants. Stability is derived from covariance of the seed map. -/
namespace Math.LinearJetEquation
set_option autoImplicit false
noncomputable section
open JetLinear JetDirections MvPolynomial

variable {S I E : Type*} [AddCommGroup E] [Module ℂ E]

def symbolMultiply (p : Symbols I) : Symbols I →ₗ[ℂ] Symbols I where
  toFun r := p * r
  map_add' _ _ := mul_add _ _ _
  map_smul' _ _ := by simp

def multiple (p : Symbols I) : Jet S I →ₗ[ℂ] Jet S I := lift (symbolMultiply p)

@[simp] theorem multiple_ofSymbols (p r : Symbols I) (s : S) :
    multiple p (ofSymbols s r) = ofSymbols s (p * r) := lift_ofSymbols _ _ _

theorem multiple_mul (p r : Symbols I) (v : Jet S I) :
    multiple p (multiple r v) = multiple (p * r) v := by
  have he : (symbolMultiply p).comp (symbolMultiply r) = symbolMultiply (p * r) := by
    apply LinearMap.ext
    intro x
    exact (mul_assoc p r x).symm
  rw [multiple, multiple, ← LinearMap.comp_apply, ← lift_comp, he]
  rfl

@[simp] theorem multiple_one : multiple (S := S) (1 : Symbols I) = LinearMap.id := by
  rw [multiple, show symbolMultiply (1 : Symbols I) = LinearMap.id by ext r; simp [symbolMultiply]]
  exact lift_id

theorem multiple_attach (p r : Symbols I) (v : JetLinear.Field S) :
    multiple p (attach r v) = attach (p * r) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single s c => simp

theorem multiple_X (i : I) : multiple (S := S) (X i) = JetLinear.shift i := by
  apply Finsupp.lhom_ext
  rintro ⟨s, α⟩ c
  rw [← ofSymbols_monomial, multiple_ofSymbols, shift_ofSymbols, mul_comm]

def relations (seed : E →ₗ[ℂ] Jet S I) : Submodule ℂ (Jet S I) :=
  Submodule.span ℂ {v | ∃ p x, multiple p (seed x) = v}

@[simp] theorem relations_zero : relations (0 : E →ₗ[ℂ] Jet S I) = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro _ ⟨p, x, rfl⟩
  simp

theorem descendant_mem (seed : E →ₗ[ℂ] Jet S I) (p : Symbols I) (x : E) :
    multiple p (seed x) ∈ relations seed := Submodule.subset_span ⟨p, x, rfl⟩

theorem seed_mem (seed : E →ₗ[ℂ] Jet S I) (x : E) : seed x ∈ relations seed := by
  simpa only [multiple_one, LinearMap.id_apply] using descendant_mem seed 1 x

theorem multiple_stable (seed : E →ₗ[ℂ] Jet S I) (p : Symbols I) :
    relations seed ≤ (relations seed).comap (multiple p) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r, x, rfl⟩
  change multiple p (multiple r (seed x)) ∈ relations seed
  rw [multiple_mul]
  exact descendant_mem seed (p * r) x

theorem shift_stable (seed : E →ₗ[ℂ] Jet S I) (i : I) :
    relations seed ≤ (relations seed).comap (JetLinear.shift i) := by
  rw [← multiple_X]
  exact multiple_stable seed (X i)

abbrev Generator (seed : E →ₗ[ℂ] Jet S I) := Jet S I ⧸ relations seed

def shift (seed : E →ₗ[ℂ] Jet S I) (i : I) : Generator seed →ₗ[ℂ] Generator seed :=
  (relations seed).mapQ (relations seed) (JetLinear.shift i) (shift_stable seed i)

@[simp] theorem shift_mk (seed : E →ₗ[ℂ] Jet S I) (i : I) (v : Jet S I) :
    shift seed i ((relations seed).mkQ v) = (relations seed).mkQ (JetLinear.shift i v) := rfl

theorem shift_commute (seed : E →ₗ[ℂ] Jet S I) (i j : I) :
    (shift seed i).comp (shift seed j) = (shift seed j).comp (shift seed i) := by
  apply LinearMap.ext
  intro v
  obtain ⟨v, rfl⟩ := (relations seed).mkQ_surjective v
  simp only [LinearMap.comp_apply, shift_mk]
  exact congrArg (relations seed).mkQ (LinearMap.congr_fun (JetLinear.shift_commute i j) v)

theorem multiple_internal (f : JetLinear.Field S →ₗ[ℂ] JetLinear.Field S)
    (p : Symbols I) (v : Jet S I) :
    JetLinear.map f (multiple p v) = multiple p (JetLinear.map f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c =>
    obtain ⟨s, α⟩ := j
    simp only [← ofSymbols_monomial, multiple_ofSymbols, internal_ofSymbols, multiple_attach]

theorem multiple_direction (f : Direction I →ₗ[ℂ] Direction I) (p : Symbols I) (v : Jet S I) :
    jetMap f (multiple p v) = multiple (symbolMap f p) (jetMap f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c =>
    obtain ⟨s, α⟩ := j
    simp only [← ofSymbols_monomial, multiple_ofSymbols, jetMap, lift_ofSymbols,
      AlgHom.toLinearMap_apply, map_mul]

theorem multiple_combined {H : Type*} [Monoid H]
    (ρ : Representation ℂ H (JetLinear.Field S)) (σ : Representation ℂ H (Direction I))
    (h : H) (p : Symbols I) (v : Jet S I) :
    combined ρ σ h (multiple p v) = multiple (symbolMap (σ h) p) (combined ρ σ h v) := by
  change JetLinear.map (ρ h) (jetMap (σ h) (multiple p v)) =
    multiple (symbolMap (σ h) p) (JetLinear.map (ρ h) (jetMap (σ h) v))
  rw [multiple_direction, multiple_internal]

section Action
variable {H : Type*} [Monoid H] (seed : E →ₗ[ℂ] Jet S I)
  (τ : Representation ℂ H E) (ρ : Representation ℂ H (JetLinear.Field S))
  (σ : Representation ℂ H (Direction I))
  (cov : ∀ h x, combined ρ σ h (seed x) = seed (τ h x))

include cov in
theorem stable (h : H) : relations seed ≤ (relations seed).comap (combined ρ σ h) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, x, rfl⟩
  change combined ρ σ h (multiple p (seed x)) ∈ relations seed
  rw [multiple_combined, cov]
  exact descendant_mem seed _ _

def action : Representation ℂ H (Generator seed) :=
  (combined ρ σ).quotient (relations seed) (stable seed τ ρ σ cov)

@[simp] theorem action_mk (h : H) (v : Jet S I) :
    action seed τ ρ σ cov h ((relations seed).mkQ v) =
      (relations seed).mkQ (combined ρ σ h v) := rfl

theorem covariance [Fintype I] (h : H) (i : I) (v : Generator seed) :
    action seed τ ρ σ cov h (shift seed i v) =
      ∑ j, (σ h (Finsupp.single i 1)) j • shift seed j (action seed τ ρ σ cov h v) := by
  obtain ⟨v, rfl⟩ := (relations seed).mkQ_surjective v
  change (relations seed).mkQ (combined ρ σ h (JetLinear.shift i v)) = _
  rw [combined_covariant, map_sum]
  simp only [map_smul]
  rfl
end Action

def scalarSeed (q : Symbols I) : JetLinear.Field S →ₗ[ℂ] Jet S I := attach q

theorem scalar_relations (q : Symbols I) : relations (scalarSeed (S := S) q) = JetEquation.relations S q := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, x, rfl⟩
    change multiple p (scalarSeed q x) ∈ JetEquation.relations S q
    rw [scalarSeed, multiple_attach]
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
    | single s c => rw [attach_single]; exact Submodule.smul_mem _ c (JetEquation.descendant_mem q s p)
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, p, rfl⟩
    simpa [scalarSeed] using descendant_mem (scalarSeed (S := S) q) p (Finsupp.single s 1)

def scalarEquiv (q : Symbols I) : Generator (scalarSeed (S := S) q) ≃ₗ[ℂ] JetEquation.Generator S q :=
  Submodule.quotEquivOfEq _ _ (scalar_relations q)

@[simp] theorem scalarEquiv_mk (q : Symbols I) (v : Jet S I) :
    scalarEquiv q ((relations (scalarSeed q)).mkQ v) = (JetEquation.relations S q).mkQ v := rfl

theorem scalarEquiv_shift (q : Symbols I) (i : I) (v : Generator (scalarSeed (S := S) q)) :
    scalarEquiv q (shift (scalarSeed q) i v) = JetEquation.shift q i (scalarEquiv q v) := by
  obtain ⟨v, rfl⟩ := (relations (scalarSeed (S := S) q)).mkQ_surjective v
  rfl

end
end Math.LinearJetEquation
