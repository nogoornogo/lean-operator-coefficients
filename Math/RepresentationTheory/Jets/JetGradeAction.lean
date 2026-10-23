import Math.RepresentationTheory.Jets.JetFunctor

/-! Order-preserving actions on the actual scalar and mixed homogeneous sources. -/
namespace Math.JetFunctor
set_option autoImplicit false
noncomputable section
open JetLinear ScalarJetAlgebra
open scoped TensorProduct

variable {S F B I H : Type*} [Group H]

theorem linearForm_order {d : ℕ} {v : Jet S I} (hv : v ∈ JetDirections.jetOrder S I d) :
    (linearForm v).IsWeightedHomogeneous weight (1, d) := by
  rw [← Finsupp.sum_single v, map_finsuppSum]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro j hj
  change linearForm (Finsupp.single j (v j)) ∈ grade 1 d
  simp only [linearForm, Finsupp.linearCombination_single]
  apply (grade 1 d).smul_mem
  change (MvPolynomial.X j).IsWeightedHomogeneous weight (1, d)
  have he : order j.2 = d := hv hj
  simpa only [weight, he] using MvPolynomial.isWeightedHomogeneous_X ℂ weight j

theorem polynomialMap_homogeneous (L : Jet S I →ₗ[ℂ] Jet S I)
    (hL : ∀ d, JetDirections.jetOrder S I d ≤ (JetDirections.jetOrder S I d).comap L)
    {g : ℕ × ℕ} {p : ScalarJetAlgebra.Algebra S I} (hp : p.IsWeightedHomogeneous weight g) :
    (polynomialMap L p).IsWeightedHomogeneous weight g := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using MvPolynomial.isWeightedHomogeneous_zero ℂ weight g
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial a c ha =>
    rw [polynomialMap, MvPolynomial.aeval_monomial]
    have hx (j : Index S I) :
        (linearForm (L (Finsupp.single j 1))).IsWeightedHomogeneous weight (weight j) :=
      linearForm_order (hL _ (Finsupp.single_mem_supported ℂ 1 rfl))
    have h := MvPolynomial.IsWeightedHomogeneous.prod a.support
      (fun j => linearForm (L (Finsupp.single j 1)) ^ a j)
      (fun j => a j • weight j) (fun j _ => (hx j).pow (a j))
    have hw : (∑ j ∈ a.support, a j • weight j) = g := ha
    rw [hw] at h
    exact h.C_mul c

def scalarGradeAction (ρ : Representation ℂ H (Jet S I))
    (hρ : ∀ h d, JetDirections.jetOrder S I d ≤ (JetDirections.jetOrder S I d).comap (ρ h))
    (n d : ℕ) : Representation ℂ H (grade (S := S) (I := I) n d) :=
  (polynomialAction ρ).subrepresentation (grade n d)
    (fun h _ hp => polynomialMap_homogeneous (ρ h) (hρ h) hp)

theorem mixedAction_odd (ρF : Representation ℂ H (Jet F I))
    (ρB : Representation ℂ H (Jet B I)) (h : H) (j : Index F I) :
    mixedAction ρF ρB h (MixedJetAlgebra.odd j) =
      oddVector (B := B) (ρF h (Finsupp.single j 1)) := by
  change ExteriorAlgebra.map (ρF h) (ExteriorAlgebra.ι ℂ (Finsupp.single j 1)) ⊗ₜ[ℂ]
    polynomialMap (ρB h) 1 = _
  rw [ExteriorAlgebra.map_apply_ι, map_one]
  rfl

theorem mixedAction_even (ρF : Representation ℂ H (Jet F I))
    (ρB : Representation ℂ H (Jet B I)) (h : H) (j : Index B I) :
    mixedAction ρF ρB h (MixedJetAlgebra.even j) =
      evenVector (F := F) (ρB h (Finsupp.single j 1)) := by
  change ExteriorAlgebra.map (ρF h) 1 ⊗ₜ[ℂ] polynomialMap (ρB h) (MvPolynomial.X j) = _
  rw [map_one, polynomialMap_X]
  rfl

variable (ρF : Representation ℂ H (Jet F I)) (ρB : Representation ℂ H (Jet B I))
  (hF : ∀ h d, JetDirections.jetOrder F I d ≤ (JetDirections.jetOrder F I d).comap (ρF h))
  (hB : ∀ h d, JetDirections.jetOrder B I d ≤ (JetDirections.jetOrder B I d).comap (ρB h))

include hF hB in
theorem mixedAction_word_mem (h : H) {n m : ℕ}
    (f : Fin n → Index F I) (b : Fin m → Index B I) :
    mixedAction ρF ρB h (MixedJetAlgebra.word f b) ∈
      MixedJetAlgebra.grade F B I n m (MixedJetAlgebra.wordOrder f b) := by
  induction n with
  | zero =>
    have hf : f = Fin.elim0 := Subsingleton.elim _ _
    subst f
    induction m with
    | zero =>
      have hb : b = Fin.elim0 := Subsingleton.elim _ _
      subst b
      rw [MixedJetAlgebra.word_empty, mixedAction_one]
      exact MixedJetAlgebra.word_empty ▸ MixedJetAlgebra.word_mem Fin.elim0 Fin.elim0
    | succ m ih =>
      rw [MixedJetAlgebra.word_cons_even, mixedAction_mul, mixedAction_even]
      have hs : Finsupp.single (b 0) (1 : ℂ) ∈ JetDirections.jetOrder B I (order (b 0).2) :=
        Finsupp.single_mem_supported ℂ 1 rfl
      have hx := evenVector_mem (F := F) (hB h _ hs)
      have hm := MixedJetAlgebra.mul_mem hx (ih (Fin.tail b))
      rw [MixedJetAlgebra.wordOrder_cons_even]
      simpa only [Nat.zero_add, Nat.one_add] using hm
  | succ n ih =>
    rw [MixedJetAlgebra.word_cons_odd, mixedAction_mul, mixedAction_odd]
    have hs : Finsupp.single (f 0) (1 : ℂ) ∈ JetDirections.jetOrder F I (order (f 0).2) :=
      Finsupp.single_mem_supported ℂ 1 rfl
    have hx := oddVector_mem (B := B) (hF h _ hs)
    have hm := MixedJetAlgebra.mul_mem hx (ih (Fin.tail f))
    rw [MixedJetAlgebra.wordOrder_cons_odd]
    simpa only [Nat.zero_add, Nat.one_add] using hm

include hF hB in
theorem mixedAction_mem (h : H) {n m d : ℕ} {p : MixedJetAlgebra.Algebra F B I}
    (hp : p ∈ MixedJetAlgebra.grade F B I n m d) :
    mixedAction ρF ρB h p ∈ MixedJetAlgebra.grade F B I n m d := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f, b, hf, rfl⟩ := hp
    simpa only [hf] using mixedAction_word_mem ρF ρB hF hB h f b
  | zero => simpa only [map_zero] using (MixedJetAlgebra.grade F B I n m d).zero_mem
  | add p q _ _ hp hq => simpa only [map_add] using Submodule.add_mem _ hp hq
  | smul c p _ hp => simpa only [map_smul] using Submodule.smul_mem _ c hp

def mixedGradeAction (n m d : ℕ) :
    Representation ℂ H (MixedJetAlgebra.grade F B I n m d) :=
  (mixedAction ρF ρB).subrepresentation (MixedJetAlgebra.grade F B I n m d)
    (fun h _ hp => mixedAction_mem ρF ρB hF hB h hp)

def sourceAction (n m : ℕ) : Representation ℂ H (MixedJetSource.Source F B I n m) :=
  (ρF.exteriorPower n).tprod (ρB.symmetricPower m)

theorem embed_action (n m : ℕ) (h : H) (p : MixedJetSource.Source F B I n m) :
    MixedJetSource.embed n m (sourceAction ρF ρB n m h p) =
      mixedAction ρF ρB h (MixedJetSource.embed n m p) := by
  have he : (MixedJetSource.embed n m).comp (sourceAction ρF ρB n m h) =
      (mixedAction ρF ρB h).comp (MixedJetSource.embed n m) := by
    apply MixedPowerDescent.ext n m
    intro v w
    simp only [LinearMap.comp_apply, sourceAction, MixedWeightSupport.pure,
      Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.exteriorPower_apply_ιMulti, Representation.symmetricPower_apply_tprod]
    change MixedJetSource.embed n m (MixedWeightSupport.pure (fun i => ρF h (v i))
      (fun j => ρB h (w j))) = mixedAction ρF ρB h
        (MixedJetSource.embed n m (MixedWeightSupport.pure v w))
    rw [MixedJetSource.embed_pure, MixedJetSource.embed_pure]
    change _ = ExteriorAlgebra.map (ρF h) (ExteriorAlgebra.ιMulti ℂ n v) ⊗ₜ[ℂ]
      polynomialMap (ρB h) (∏ j, SymmetricPolynomialPower.linearForm (w j))
    rw [ExteriorAlgebra.map_apply_ιMulti, map_prod]
    apply congrArg₂ (fun (x : MixedJetAlgebra.Odd F I) (y : MixedJetAlgebra.Even B I) => x ⊗ₜ[ℂ] y)
    · rfl
    · apply Finset.prod_congr rfl
      intro j _
      exact (polynomialMap_linearForm (ρB h) (w j)).symm
  exact LinearMap.congr_fun he p

@[reducible] local instance (n m : ℕ) :
    AddCommGroup (MixedJetSource.Source F B I n m) := inferInstance
@[reducible] local instance (n m : ℕ) :
    Module ℂ (MixedJetSource.Source F B I n m) := inferInstance

def sourceGradeAction (n m d : ℕ) :
    Representation ℂ H (MixedJetSource.sourceGrade F B I n m d) :=
  (sourceAction ρF ρB n m).subrepresentation (MixedJetSource.sourceGrade F B I n m d)
    (fun h p hp => by
      change MixedJetSource.embed n m (sourceAction ρF ρB n m h p) ∈
        MixedJetAlgebra.grade F B I n m d
      rw [embed_action]
      exact mixedAction_mem ρF ρB hF hB h hp)

def gradeRepresentationEquiv (n m d : ℕ) :
    Representation.Equiv (sourceGradeAction ρF ρB hF hB n m d)
      (mixedGradeAction ρF ρB hF hB n m d) :=
  Representation.Equiv.mk (MixedJetSource.gradeEquiv n m d) (by
    intro h
    apply LinearMap.ext
    intro p
    exact Subtype.ext (embed_action ρF ρB n m h p.val))

end
end Math.JetFunctor
