import Physics.FieldTheory.Jets.Weyl.Equations.WeylEquationControls
import Math.Algebra.Jets.JetConjugation

/-! Actual right-Weyl source equations obtained by conjugating the left system. -/
namespace Physics.ConjugateWeylEquation
set_option autoImplicit false
noncomputable section
open Math JetLinear JetDirections WeylLinearEquation
open JetConjugation

def equationConjugation : Equations →ₛₗ[starRingEnd ℂ] Equations where
  toFun f := {
    toFun v := star (f (star v))
    map_add' v w := by simp
    map_smul' c v := by simp }
  map_add' f h := by ext v; simp
  map_smul' c f := by ext v; simp

@[simp] theorem equationConjugation_apply (f : Equations) (v : Spinor) :
    equationConjugation f v = star (f (star v)) := rfl

@[simp] theorem equationConjugation_involutive (f : Equations) :
    equationConjugation (equationConjugation f) = f := by ext v; simp

theorem spinor_conjugation (g : Group) (v : Spinor) :
    star (WeylSpinor.left g v) = WeylSpinor.right g (star v) := by
  ext i
  change star (((g : LorentzDirections.Mat).mulVec v) i) = _
  simp [WeylSpinor.right_apply, Matrix.mulVec, dotProduct]

theorem field_conjugation (g : Group) (v : JetLinear.Field (Fin 2)) :
    coefficients (LorentzJetIBP.weyl false g v) = LorentzJetIBP.weyl true g (coefficients v) := by
  apply LorentzJetIBP.spinorBasis.injective
  have hc (w : JetLinear.Field (Fin 2)) : LorentzJetIBP.spinorBasis (coefficients w) =
      star (LorentzJetIBP.spinorBasis w) := by ext i; rfl
  rw [hc, LorentzJetIBP.weyl_basis, LorentzJetIBP.weyl_basis, hc]
  exact spinor_conjugation g _

theorem direction_real (g : Group) (i : Fin 4) :
    coefficients (LorentzDirections.direction g (Finsupp.single i 1)) =
      LorentzDirections.direction g (Finsupp.single i 1) := by
  ext j
  rw [coefficients_apply, LorentzDirections.direction_single]
  have h := congrFun (LorentzDirections.vector_preserves_real g⁻¹ (Pi.single j (1 : ℝ))) i
  have he : (fun k => (((Pi.single j (1 : ℝ) : Fin 4 → ℝ) k) : ℂ)) = Pi.single j 1 := by
    ext k
    by_cases hk : k = j <;> simp [hk]
  rw [he] at h
  exact h

theorem jet_conjugation (g : Group) (v : Jets) :
    coefficients (combined (LorentzJetIBP.weyl false) LorentzDirections.direction g v) =
      combined (LorentzJetIBP.weyl true) LorentzDirections.direction g (coefficients v) := by
  change coefficients (JetLinear.map (LorentzJetIBP.weyl false g)
    (jetMap (LorentzDirections.direction g) v)) = _
  rw [coefficients_internal _ _ (field_conjugation g), coefficients_direction _ (direction_real g)]
  rfl

theorem equation_action (g : Group) (f : Equations) :
    equationConjugation (WeylSpinor.right.dual g f) =
      WeylSpinor.left.dual g (equationConjugation f) := by
  apply LinearMap.ext
  intro v
  change star (f (WeylSpinor.right g⁻¹ (star v))) = star (f (star (WeylSpinor.left g⁻¹ v)))
  rw [spinor_conjugation]

def rightSeed : Equations →ₗ[ℂ] Jets where
  toFun f := coefficients (seed (equationConjugation f))
  map_add' f h := by simp only [map_add]
  map_smul' c f := by simp [map_smulₛₗ]

theorem rightSeed_covariant (g : Group) (f : Equations) :
    combined (LorentzJetIBP.weyl true) LorentzDirections.direction g (rightSeed f) =
      rightSeed (WeylSpinor.left.dual g f) := by
  change combined (LorentzJetIBP.weyl true) LorentzDirections.direction g
    (coefficients (seed (equationConjugation f))) = _
  rw [← jet_conjugation, seed_covariant]
  have h := congrArg equationConjugation (equation_action g (equationConjugation f))
  simp only [equationConjugation_involutive] at h
  change coefficients (seed _) = coefficients (seed _)
  rw [← h]

@[simp] theorem equationConjugation_row (b : Fin 2) : equationConjugation (row b) = row b := by
  apply LinearMap.ext
  intro v
  simp [row]

theorem rightSeed_row_zero : rightSeed (row 0) =
    ofSymbols (0 : Fin 2) (MvPolynomial.X (0 : Fin 4) + MvPolynomial.X 3) +
    ofSymbols (1 : Fin 2) (MvPolynomial.X (1 : Fin 4) - Complex.I • MvPolynomial.X 2) := by
  simp [rightSeed, seed_row_zero, coefficients_ofSymbols, symbols, MvPolynomial.smul_eq_C_mul,
    sub_eq_add_neg]

theorem rightSeed_row_one : rightSeed (row 1) =
    ofSymbols (0 : Fin 2) (MvPolynomial.X (1 : Fin 4) + Complex.I • MvPolynomial.X 2) +
    ofSymbols (1 : Fin 2) (MvPolynomial.X (0 : Fin 4) - MvPolynomial.X 3) := by
  simp [rightSeed, seed_row_one, coefficients_ofSymbols, symbols, MvPolynomial.smul_eq_C_mul]

abbrev rightRelations := LinearJetEquation.relations rightSeed
abbrev RightGenerator := LinearJetEquation.Generator rightSeed
def rightAction := LinearJetEquation.action rightSeed WeylSpinor.left.dual
  (LorentzJetIBP.weyl true) LorentzDirections.direction rightSeed_covariant

theorem conjugate_relations {v : Jets} (hv : v ∈ relations) : coefficients v ∈ rightRelations := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p, f, rfl⟩ := hv
    rw [coefficients_multiple]
    have he : coefficients (seed f) = rightSeed (equationConjugation f) := by simp [rightSeed]
    rw [he]
    exact LinearJetEquation.descendant_mem rightSeed _ _
  | zero => simp
  | add v w hv hw ihv ihw => simpa only [map_add] using rightRelations.add_mem ihv ihw
  | smul c v hv ih =>
    rw [map_smulₛₗ]
    exact rightRelations.smul_mem _ ih

theorem conjugate_right_relations {v : Jets} (hv : v ∈ rightRelations) : coefficients v ∈ relations := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p, f, rfl⟩ := hv
    rw [coefficients_multiple]
    change LinearJetEquation.multiple (symbols p) (coefficients (coefficients (seed (equationConjugation f)))) ∈ relations
    rw [coefficients_involutive]
    exact LinearJetEquation.descendant_mem seed _ _
  | zero => simp
  | add v w hv hw ihv ihw => simpa only [map_add] using relations.add_mem ihv ihw
  | smul c v hv ih =>
    rw [map_smulₛₗ]
    exact relations.smul_mem _ ih

theorem conjugate_relations_iff (v : Jets) : coefficients v ∈ rightRelations ↔ v ∈ relations :=
  ⟨fun h => by simpa using conjugate_right_relations h, conjugate_relations⟩

def toRight : Generator →ₛₗ[starRingEnd ℂ] RightGenerator :=
  relations.mapQ rightRelations coefficients (fun _ hv => conjugate_relations hv)

def toLeft : RightGenerator →ₛₗ[starRingEnd ℂ] Generator :=
  rightRelations.mapQ relations coefficients (fun _ hv => conjugate_right_relations hv)

@[simp] theorem toLeft_toRight (x : Generator) : toLeft (toRight x) = x := by
  obtain ⟨v, rfl⟩ := relations.mkQ_surjective x
  change relations.mkQ (coefficients (coefficients v)) = relations.mkQ v
  rw [coefficients_involutive]

@[simp] theorem toRight_toLeft (x : RightGenerator) : toRight (toLeft x) = x := by
  obtain ⟨v, rfl⟩ := rightRelations.mkQ_surjective x
  change rightRelations.mkQ (coefficients (coefficients v)) = rightRelations.mkQ v
  rw [coefficients_involutive]

theorem toRight_shift (i : Fin 4) (x : Generator) :
    toRight (LinearJetEquation.shift seed i x) = LinearJetEquation.shift rightSeed i (toRight x) := by
  obtain ⟨v, rfl⟩ := relations.mkQ_surjective x
  exact congrArg rightRelations.mkQ (coefficients_shift i v)

theorem toLeft_shift (i : Fin 4) (x : RightGenerator) :
    toLeft (LinearJetEquation.shift rightSeed i x) = LinearJetEquation.shift seed i (toLeft x) := by
  obtain ⟨v, rfl⟩ := rightRelations.mkQ_surjective x
  exact congrArg relations.mkQ (coefficients_shift i v)

theorem toRight_action (g : Group) (x : Generator) : toRight (WeylLinearEquation.action g x) =
    rightAction g (toRight x) := by
  obtain ⟨v, rfl⟩ := relations.mkQ_surjective x
  exact congrArg rightRelations.mkQ (jet_conjugation g v)

theorem toLeft_action (g : Group) (x : RightGenerator) : toLeft (rightAction g x) =
    WeylLinearEquation.action g (toLeft x) := by
  have h := congrArg toLeft (toRight_action g (toLeft x))
  simpa only [toLeft_toRight, toRight_toLeft] using h.symm

theorem right_higher_jet_survives (k : ℕ) :
    rightRelations.mkQ (ofSymbols (1 : Fin 2) (MvPolynomial.X (0 : Fin 4) ^ k)) ≠ 0 := by
  intro hz
  have he := congrArg toLeft hz
  rw [map_zero] at he
  change relations.mkQ (coefficients (ofSymbols (1 : Fin 2) (MvPolynomial.X (0 : Fin 4) ^ k))) = 0 at he
  rw [coefficients_ofSymbols] at he
  apply higher_jet_survives k
  simpa [symbols] using he

end
end Physics.ConjugateWeylEquation
