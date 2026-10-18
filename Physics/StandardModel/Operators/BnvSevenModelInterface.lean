import Physics.StandardModel.Operators.BnvSevenCompleteness

open Math

/-! Species-preserving actual-field identifications transport the independent
mixed input, not merely an already restricted contraction ansatz. -/
namespace GUT.BnvSevenModelInterface
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor BnvMixedInput DeltaLOneSignedInput

variable {G : Type*} [Group G]
  {A A' : Species → Type*} [∀ s, AddCommGroup (A s)] [∀ s, Module ℂ (A s)]
  [∀ s, AddCommGroup (A' s)] [∀ s, Module ℂ (A' s)]
  {B B' : ScalarSpecies → Type*} [∀ s, AddCommGroup (B s)] [∀ s, Module ℂ (B s)]
  [∀ s, AddCommGroup (B' s)] [∀ s, Module ℂ (B' s)]
  {r : ∀ s, Representation ℂ G (A s)} {r' : ∀ s, Representation ℂ G (A' s)}
  {t : ∀ s, Representation ℂ G (B s)} {t' : ∀ s, Representation ℂ G (B' s)}
  (e : ∀ s, Representation.Equiv (r s) (r' s))
  (h : ∀ s, Representation.Equiv (t s) (t' s))

def piEquiv {I : Type*} [Fintype I] [DecidableEq I] {V W : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {a : ∀ i, Representation ℂ G (V i)} {b : ∀ i, Representation ℂ G (W i)}
    (f : ∀ i, Representation.Equiv (a i) (b i)) : Representation.Equiv
    (FiniteSpeciesExterior.representation a) (FiniteSpeciesExterior.representation b) where
  toLinearEquiv := LinearEquiv.piCongrRight (fun i => (f i).toLinearEquiv)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext i
    exact LinearMap.congr_fun ((f i).isIntertwining' g) (x i)

theorem pi_single {I : Type*} [Fintype I] [DecidableEq I] {V W : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {a : ∀ i, Representation ℂ G (V i)} {b : ∀ i, Representation ℂ G (W i)}
    (f : ∀ i, Representation.Equiv (a i) (b i)) (s : I) (v : V s) :
    piEquiv f (Pi.single s v) = Pi.single s (f s v) := by
  funext j
  change f j (Pi.single s v j) = Pi.single s (f s v) j
  by_cases hj : j = s
  · subst j; simp
  · simp [hj]

def mixedEquiv (n m : ℕ) :=
  tensorEquiv ((piEquiv e).exteriorPower n) ((piEquiv h).symmetricPower m)

def coefficientEquiv (n m : ℕ) := InvariantCoefficientTransport.alongEquiv (mixedEquiv e h n m)

def sector (n m : ℕ) : Submodule ℂ (MixedWeightSupport.Coefficient
    (FiniteSpeciesExterior.representation r) (FiniteSpeciesExterior.representation t) (n := n) (m := m)) where
  carrier := {f | ∀ (labels : Fin n → Species) (scalars : Fin m → ScalarSpecies)
    (v : ∀ i, A (labels i)) (w : ∀ j, B (scalars j)),
    (∑ i, baryon (labels i)) = 0 →
      f (MixedWeightSupport.pure (fun i => Pi.single (labels i) (v i))
        (fun j => Pi.single (scalars j) (w j))) = 0}
  zero_mem' := by intro labels scalars v w hb; rfl
  add_mem' := by
    intro f g hf hg labels scalars v w hb
    change f _ + g _ = 0
    rw [hf labels scalars v w hb, hg labels scalars v w hb, add_zero]
  smul_mem' := by
    intro z f hf labels scalars v w hb
    change z * f _ = 0
    rw [hf labels scalars v w hb, mul_zero]

theorem pull_mem {n m : ℕ} (f : sector (r := r') (t := t') n m) :
    f.val.comp (mixedEquiv e h n m).toIntertwiningMap ∈ sector (r := r) (t := t) n m := by
  intro labels scalars v w hb
  change f.val ((mixedEquiv e h n m)
    (MixedWeightSupport.pure (fun i => Pi.single (labels i) (v i))
      (fun j => Pi.single (scalars j) (w j)))) = 0
  change f.val (((piEquiv e).exteriorPower n)
    (exteriorPower.ιMulti ℂ n (fun i => Pi.single (labels i) (v i))) ⊗ₜ[ℂ]
    ((piEquiv h).symmetricPower m)
      (SymmetricPower.tprod ℂ (fun j => Pi.single (scalars j) (w j)))) = 0
  simp only [Representation.Equiv.exteriorPower_apply_ιMulti,
    Representation.Equiv.symmetricPower_apply_tprod]
  have hv : (piEquiv e ∘ fun i => Pi.single (labels i) (v i)) =
    (fun i => Pi.single (labels i) (e (labels i) (v i))) := by
    funext i
    exact pi_single e (labels i) (v i)
  have hw : (piEquiv h ∘ fun j => Pi.single (scalars j) (w j)) =
    (fun j => Pi.single (scalars j) (h (scalars j) (w j))) := by
    funext j
    exact pi_single h (scalars j) (w j)
  change (fun j => piEquiv h (Pi.single (scalars j) (w j))) = _ at hw
  rw [hv, hw]
  exact f.property labels scalars _ _ hb

def pull {n m : ℕ} (f : sector (r := r') (t := t') n m) : sector (r := r) (t := t) n m :=
  ⟨f.val.comp (mixedEquiv e h n m).toIntertwiningMap, pull_mem e h f⟩

theorem pull_symm {n m : ℕ} (f : sector (r := r) (t := t) n m) :
    pull e h (pull (fun s => (e s).symm) (fun s => (h s).symm) f) = f := by
  apply Subtype.ext
  apply MixedWeightSupport.ext
  intro v w
  change f.val ((mixedEquiv (fun s => (e s).symm) (fun s => (h s).symm) n m)
    ((mixedEquiv e h n m) (MixedWeightSupport.pure v w))) = f.val (MixedWeightSupport.pure v w)
  have hm (ee : ∀ s, Representation.Equiv (r s) (r' s))
      (hh : ∀ s, Representation.Equiv (t s) (t' s))
      (v : Fin n → ∀ s, A s) (w : Fin m → ∀ s, B s) :
      mixedEquiv ee hh n m (MixedWeightSupport.pure v w) =
      MixedWeightSupport.pure (fun i => piEquiv ee (v i)) (fun j => piEquiv hh (w j)) := by
    change ((piEquiv ee).exteriorPower n) (exteriorPower.ιMulti ℂ n v) ⊗ₜ[ℂ]
      ((piEquiv hh).symmetricPower m) (SymmetricPower.tprod ℂ w) = _
    rw [Representation.Equiv.exteriorPower_apply_ιMulti,
      Representation.Equiv.symmetricPower_apply_tprod]
    rfl
  rw [hm]
  change f.val (((piEquiv (fun s => (e s).symm)).exteriorPower n)
    (exteriorPower.ιMulti ℂ n (fun i => piEquiv e (v i))) ⊗ₜ[ℂ]
    ((piEquiv (fun s => (h s).symm)).symmetricPower m)
      (SymmetricPower.tprod ℂ (fun j => piEquiv h (w j)))) = _
  rw [Representation.Equiv.exteriorPower_apply_ιMulti,
    Representation.Equiv.symmetricPower_apply_tprod]
  congr 2
  · congr 1
    funext i
    funext s
    exact (e s).toLinearEquiv.symm_apply_apply (v i s)
  · congr 1
    funext j
    funext s
    exact (h s).toLinearEquiv.symm_apply_apply (w j s)

def sectorEquiv (n m : ℕ) : sector (r := r') (t := t') n m ≃ₗ[ℂ]
    sector (r := r) (t := t) n m where
  toFun := pull e h
  invFun := pull (fun s => (e s).symm) (fun s => (h s).symm)
  left_inv f := pull_symm (fun s => (e s).symm) (fun s => (h s).symm) f
  right_inv f := pull_symm e h f
  map_add' f g := by apply Subtype.ext; ext v; rfl
  map_smul' z f := by apply Subtype.ext; ext v; rfl

/-- Actual fields retain the same signed alphabet and engineering weights. -/
def bounded (dimension : ℕ) : Submodule ℂ
    (∀ nm : Fin 8 × Fin 12, sector (r := r) (t := t) nm.1.val nm.2.val) where
  carrier := {f | ∀ nm, 2 * dimension < 3 * nm.1.val + 2 * nm.2.val → f nm = 0}
  zero_mem' := by intro nm hd; rfl
  add_mem' := by
    intro f g hf hg nm hd
    change f nm + g nm = 0
    rw [hf nm hd, hg nm hd, add_zero]
  smul_mem' := by
    intro z f hf nm hd
    change z • f nm = 0
    rw [hf nm hd, smul_zero]

def boundedEquiv (dimension : ℕ) : bounded (r := r') (t := t') dimension ≃ₗ[ℂ]
    bounded (r := r) (t := t) dimension where
  toFun f := ⟨fun nm => sectorEquiv e h nm.1.val nm.2.val (f.val nm), by
    intro nm hd
    change sectorEquiv e h nm.1.val nm.2.val (f.val nm) = 0
    rw [f.property nm hd]
    exact (sectorEquiv e h nm.1.val nm.2.val).map_zero⟩
  invFun f := ⟨fun nm => (sectorEquiv e h nm.1.val nm.2.val).symm (f.val nm), by
    intro nm hd
    change (sectorEquiv e h nm.1.val nm.2.val).symm (f.val nm) = 0
    rw [f.property nm hd]
    exact (sectorEquiv e h nm.1.val nm.2.val).symm.map_zero⟩
  left_inv f := by
    apply Subtype.ext
    funext nm
    exact (sectorEquiv e h nm.1.val nm.2.val).symm_apply_apply (f.val nm)
  right_inv f := by
    apply Subtype.ext
    funext nm
    exact (sectorEquiv e h nm.1.val nm.2.val).apply_symm_apply (f.val nm)
  map_add' f g := by
    apply Subtype.ext
    funext nm
    exact (sectorEquiv e h nm.1.val nm.2.val).map_add _ _
  map_smul' z f := by
    apply Subtype.ext
    funext nm
    exact (sectorEquiv e h nm.1.val nm.2.val).map_smul z _

end

noncomputable section StandardModel
open Representation BnvMixedInput DeltaLOneSignedInput
variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  {S : ScalarSpecies → Type*} [∀ s, AddCommGroup (S s)] [∀ s, Module ℂ (S s)]
  (flavor : ∀ s, Representation ℂ R (F s))
  (scalarFlavor : ∀ s, Representation ℂ R (S s))
  {V : Species → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {W : ScalarSpecies → Type*} [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  {actual : ∀ s, Representation ℂ ((StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × R) (V s)}
  {actualScalar : ∀ s, Representation ℂ ((StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × R) (W s)}
  (fields : ∀ s, Representation.Equiv (DeltaLOneSignedFields.field flavor s) (actual s))
  (scalars : ∀ s, Representation.Equiv (scalarField scalarFlavor s) (actualScalar s))

/-- A species-preserving field dictionary suffices for the complete endpoint. -/
def residualEquiv : bounded (r := actual) (t := actualScalar) 7 ≃ₗ[ℂ]
    BnvSevenCompleteness.ResidualProduct flavor scalarFlavor :=
  (boundedEquiv fields scalars 7).trans (BnvSevenCompleteness.equiv flavor scalarFlavor)

include fields scalars in
theorem forbidden_iff : (∀ f : bounded (r := actual) (t := actualScalar) 7, f = 0) ↔
    (∀ q : BnvSixResidualCompleteness.ResidualProduct flavor, q = 0) ∧
      (∀ i, ∀ q : BnvSevenSignedCoordinates.Factor flavor scalarFlavor i, q = 0) := by
  rw [← BnvSevenCompleteness.forbidden_iff flavor scalarFlavor]
  constructor
  · intro hz f
    exact (boundedEquiv fields scalars 7).symm.injective
      ((hz ((boundedEquiv fields scalars 7).symm f)).trans
        (boundedEquiv fields scalars 7).symm.map_zero.symm)
  · intro hz f
    exact (boundedEquiv fields scalars 7).injective
      ((hz ((boundedEquiv fields scalars 7) f)).trans
        (boundedEquiv fields scalars 7).map_zero.symm)
end StandardModel
end GUT.BnvSevenModelInterface
