import Math.RepresentationTheory.Jets.MixedJetSource

/-! Degree zero recovers the existing derivative-free mixed tensor source,
with an actual inverse rather than identifying all higher jets with zero. -/
namespace Math.MixedJetSource
set_option autoImplicit false
noncomputable section
open JetLinear MixedJetAlgebra
open scoped TensorProduct

variable {F B I : Type*}

abbrev Original (F B : Type*) (n m : ℕ) :=
  MixedPowerDescent.Domain (A := JetLinear.Field F) (B := JetLinear.Field B) n m

@[reducible] local instance (n m : ℕ) : AddCommGroup (Original F B n m) := inferInstance
@[reducible] local instance (n m : ℕ) : Module ℂ (Original F B n m) := inferInstance
@[reducible] local instance (n m : ℕ) : AddCommGroup (Source F B I n m) := inferInstance
@[reducible] local instance (n m : ℕ) : Module ℂ (Source F B I n m) := inferInstance

def forget : Jet F I →ₗ[ℂ] JetLinear.Field F := Finsupp.lmapDomain ℂ ℂ Prod.fst

@[simp] theorem forget_atOrder (α : I →₀ ℕ) (v : JetLinear.Field F) :
    forget (atOrder α v) = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single s c => simp [forget]

def zeroMap (n m : ℕ) : Original F B n m →ₗ[ℂ] Source F B I n m :=
  TensorProduct.map (exteriorPower.map n (atOrder 0)) (SymmetricPower.map (atOrder 0))

def forgetMap (n m : ℕ) : Source F B I n m →ₗ[ℂ] Original F B n m :=
  TensorProduct.map (exteriorPower.map n forget) (SymmetricPower.map forget)

theorem forgetMap_zeroMap (n m : ℕ) :
    (forgetMap (I := I) n m).comp (zeroMap n m) = (LinearMap.id : Original F B n m →ₗ[ℂ] _) := by
  apply MixedPowerDescent.ext (A := JetLinear.Field F) (B := JetLinear.Field B)
    (N := Original F B n m) n m
  intro v w
  simp [zeroMap, forgetMap, MixedWeightSupport.pure, TensorProduct.map_tmul,
    exteriorPower.map_apply_ιMulti, SymmetricPower.map_tprod, Function.comp_def]

theorem zeroMap_injective (n m : ℕ) : Function.Injective (zeroMap (F := F) (B := B) (I := I) n m) := by
  apply Function.LeftInverse.injective (g := forgetMap n m)
  intro p
  exact LinearMap.congr_fun (forgetMap_zeroMap n m) p

def zeroEmbed (n m : ℕ) : Original F B n m →ₗ[ℂ] Algebra F B I :=
  (embed n m).comp (zeroMap n m)

theorem zeroEmbed_pure (n m : ℕ) (v : Fin n → JetLinear.Field F) (w : Fin m → JetLinear.Field B) :
    zeroEmbed n m (MixedWeightSupport.pure v w) = wordVectors
      (fun _ : Fin n => (0 : I →₀ ℕ)) (fun _ : Fin m => 0) v w := by
  simp only [zeroEmbed, LinearMap.comp_apply, zeroMap, MixedWeightSupport.pure,
    TensorProduct.map_tmul, exteriorPower.map_apply_ιMulti, SymmetricPower.map_tprod]
  change embed n m (MixedWeightSupport.pure (atOrder 0 ∘ v) (atOrder 0 ∘ w)) = _
  rw [embed_pure]
  rfl

theorem zeroEmbed_mem (n m : ℕ) (p : Original F B n m) :
    zeroEmbed (I := I) n m p ∈ grade F B I n m 0 := by
  have he : (grade F B I n m 0).mkQ.comp (zeroEmbed n m) = 0 := by
    apply MixedPowerDescent.ext (A := JetLinear.Field F) (B := JetLinear.Field B) n m
    intro v w
    rw [LinearMap.comp_apply, zeroEmbed_pure]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    simpa [ScalarJetAlgebra.order] using wordVectors_mem
      (fun _ : Fin n => (0 : I →₀ ℕ)) (fun _ : Fin m => 0) v w
  exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun he p)

private theorem index_zero {S : Type*} (j : ScalarJetAlgebra.Index S I)
    (h : ScalarJetAlgebra.order j.2 = 0) : (j.1, (0 : I →₀ ℕ)) = j := by
  have ha : j.2 = 0 := by
    ext i
    have hi := Finsupp.le_weight (fun _ : I => 1) (s := i) (by decide) j.2
    change j.2 i ≤ ScalarJetAlgebra.order j.2 at hi
    rw [h] at hi
    exact Nat.eq_zero_of_le_zero hi
  exact Prod.ext rfl ha.symm

theorem zeroGrade_le_range (n m : ℕ) : grade F B I n m 0 ≤ (zeroEmbed n m).range := by
  apply Submodule.span_le.mpr
  rintro p ⟨f, b, hf, rfl⟩
  refine ⟨MixedWeightSupport.pure (fun i => Finsupp.single (f i).1 1)
    (fun j => Finsupp.single (b j).1 1), ?_⟩
  rw [zeroEmbed_pure]
  simp only [wordVectors, atOrder_single, linearForm, Finsupp.linearCombination_single, one_smul, word]
  apply congrArg₂ (fun (x : Odd F I) (y : Even B I) => x ⊗ₜ[ℂ] y)
  · apply congrArg (ExteriorAlgebra.ιMulti ℂ n)
    funext i
    rw [index_zero (f i) (Nat.eq_zero_of_le_zero (by simpa only [hf] using odd_order_le f b i))]
  · apply Finset.prod_congr rfl
    intro j _
    rw [index_zero (b j) (Nat.eq_zero_of_le_zero (by simpa only [hf] using even_order_le f b j))]

def zeroGradeMap (n m : ℕ) : Original F B n m →ₗ[ℂ] grade F B I n m 0 where
  toFun p := ⟨zeroEmbed n m p, zeroEmbed_mem n m p⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

def zeroEquiv (n m : ℕ) : Original F B n m ≃ₗ[ℂ] grade F B I n m 0 :=
  LinearEquiv.ofBijective (zeroGradeMap n m) ⟨by
    intro p q h
    exact zeroMap_injective n m (embed_injective n m (congrArg Subtype.val h)), by
    intro p
    obtain ⟨x, hx⟩ := zeroGrade_le_range n m p.property
    exact ⟨x, Subtype.ext hx⟩⟩

def zeroCoefficientEquiv {W : Type*} [AddCommGroup W] [Module ℂ W] (n m : ℕ) :
    (Original F B n m →ₗ[ℂ] W) ≃ₗ[ℂ] (grade F B I n m 0 →ₗ[ℂ] W) :=
  LinearEquiv.arrowCongr (zeroEquiv n m) (LinearEquiv.refl ℂ W)

def originalAction {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (n m : ℕ) :
    Representation ℂ H (Original F B n m) := (ρF.exteriorPower n).tprod (ρB.symmetricPower m)

theorem zeroMap_action {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (n m : ℕ) (h : H) (p : Original F B n m) :
    zeroMap (I := I) n m (originalAction ρF ρB n m h p) =
      sourceAction ρF ρB n m h (zeroMap n m p) := by
  have he : (zeroMap (I := I) n m).comp (originalAction ρF ρB n m h) =
      (sourceAction ρF ρB n m h).comp (zeroMap n m) := by
    apply MixedPowerDescent.ext (A := JetLinear.Field F) (B := JetLinear.Field B) n m
    intro v w
    simp [originalAction, sourceAction, zeroMap, MixedWeightSupport.pure,
      Representation.tprod_apply, TensorProduct.map_tmul, exteriorPower.map_apply_ιMulti,
      SymmetricPower.map_tprod, JetLinear.map_atOrder, Function.comp_def,
      JetLinear.action]
  exact LinearMap.congr_fun he p

theorem zeroEquiv_action {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (n m : ℕ) (h : H) (p : Original F B n m) :
    zeroEquiv (I := I) n m (originalAction ρF ρB n m h p) =
      gradeAction ρF ρB n m 0 h (zeroEquiv n m p) := by
  apply Subtype.ext
  change embed n m (zeroMap n m (originalAction ρF ρB n m h p)) =
    action ρF ρB h (embed n m (zeroMap (I := I) n m p))
  rw [zeroMap_action, embed_action]

def zeroRepresentationEquiv {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (n m : ℕ) :
    Representation.Equiv (originalAction ρF ρB n m) (gradeAction (I := I) ρF ρB n m 0) :=
  Representation.Equiv.mk (zeroEquiv n m) (by
    intro h
    apply LinearMap.ext
    exact zeroEquiv_action ρF ρB n m h)

end
end Math.MixedJetSource
