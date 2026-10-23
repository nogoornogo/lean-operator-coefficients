import Math.Algebra.Jets.MixedJetGrading
import Math.RepresentationTheory.Jets.MixedJetAction
import Math.LinearAlgebra.Symmetric.SymmetricPolynomialPower
import Mathlib.RingTheory.Flat.Basic

/-! Injective connection from the existing statistics-constrained mixed tensor
source to the actual jet algebra, and inverse transport on every derivative grade. -/
namespace Math.MixedJetSource
set_option autoImplicit false
noncomputable section
open JetLinear MixedJetAlgebra
open scoped TensorProduct

variable {F B I : Type*}

abbrev Source (F B I : Type*) (n m : ℕ) :=
  MixedPowerDescent.Domain (A := Jet F I) (B := Jet B I) n m

def embed (n m : ℕ) : Source F B I n m →ₗ[ℂ] MixedJetAlgebra.Algebra F B I :=
  TensorProduct.map (Submodule.subtype (⋀[ℂ]^n (Jet F I)))
    ((MvPolynomial.homogeneousSubmodule (ScalarJetAlgebra.Index B I) ℂ m).subtype.comp
      (SymmetricPolynomialPower.equiv m).toLinearMap)

theorem embed_injective (n m : ℕ) : Function.Injective (embed (F := F) (B := B) (I := I) n m) :=
  TensorProduct.map_injective_of_flat_flat _ _ (Submodule.subtype_injective _)
    ((Submodule.subtype_injective _).comp (SymmetricPolynomialPower.equiv m).injective)

theorem embed_pure (n m : ℕ) (v : Fin n → Jet F I) (w : Fin m → Jet B I) :
    embed n m (MixedWeightSupport.pure v w) =
      ExteriorAlgebra.ιMulti ℂ n v ⊗ₜ[ℂ] ∏ j, SymmetricPolynomialPower.linearForm (w j) := by
  simp only [embed, MixedWeightSupport.pure, TensorProduct.map_tmul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe,
    SymmetricPolynomialPower.equiv_pure]

theorem embed_word (n m : ℕ) (f : Fin n → ScalarJetAlgebra.Index F I)
    (b : Fin m → ScalarJetAlgebra.Index B I) :
    embed n m (MixedWeightSupport.pure (fun i => Finsupp.single (f i) 1)
      (fun j => Finsupp.single (b j) 1)) = word f b := by
  simp [embed_pure, word, SymmetricPolynomialPower.linearForm]

def countGrade (F B I : Type*) (n m : ℕ) : Submodule ℂ (MixedJetAlgebra.Algebra F B I) :=
  (embed (F := F) (B := B) (I := I) n m).range

def sourceEquiv (n m : ℕ) : Source F B I n m ≃ₗ[ℂ] countGrade F B I n m :=
  LinearEquiv.ofInjective (embed n m) (embed_injective n m)

theorem grade_le_count (n m d : ℕ) : grade F B I n m d ≤ countGrade F B I n m := by
  apply Submodule.span_le.mpr
  rintro p ⟨f, b, _, rfl⟩
  exact ⟨MixedWeightSupport.pure (fun i => Finsupp.single (f i) 1)
    (fun j => Finsupp.single (b j) 1), embed_word n m f b⟩

def sourceGrade (F B I : Type*) (n m d : ℕ) : Submodule ℂ (Source F B I n m) :=
  (grade F B I n m d).comap (embed n m)

def sourceGradeMap (n m d : ℕ) : sourceGrade F B I n m d →ₗ[ℂ] grade F B I n m d where
  toFun p := ⟨embed n m p.val, p.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

def gradeEquiv (n m d : ℕ) : sourceGrade F B I n m d ≃ₗ[ℂ] grade F B I n m d :=
  LinearEquiv.ofBijective (sourceGradeMap n m d) ⟨by
    intro x y h
    exact Subtype.ext (embed_injective n m (congrArg Subtype.val h)), by
    intro p
    obtain ⟨x, hx⟩ := grade_le_count n m d p.property
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change embed n m x ∈ grade F B I n m d
    rw [hx]; exact p.property⟩

def coefficientEquiv {W : Type*} [AddCommGroup W] [Module ℂ W] (n m d : ℕ) :
    (sourceGrade F B I n m d →ₗ[ℂ] W) ≃ₗ[ℂ] (grade F B I n m d →ₗ[ℂ] W) :=
  LinearEquiv.arrowCongr (gradeEquiv n m d) (LinearEquiv.refl ℂ W)

@[simp] theorem coefficientEquiv_apply {W : Type*} [AddCommGroup W] [Module ℂ W] (n m d : ℕ)
    (f : sourceGrade F B I n m d →ₗ[ℂ] W) (p : sourceGrade F B I n m d) :
    coefficientEquiv n m d f (gradeEquiv n m d p) = f p := by
  simp [coefficientEquiv]

@[simp] theorem coefficientEquiv_symm {W : Type*} [AddCommGroup W] [Module ℂ W] (n m d : ℕ)
    (f : grade F B I n m d →ₗ[ℂ] W) (p : sourceGrade F B I n m d) :
    (coefficientEquiv n m d).symm f p = f (gradeEquiv n m d p) := rfl

def sourceAction {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (n m : ℕ) :
    Representation ℂ H (Source F B I n m) :=
  ((JetLinear.action ρF).exteriorPower n).tprod ((JetLinear.action ρB).symmetricPower m)

theorem embed_action {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (n m : ℕ) (h : H) (p : Source F B I n m) :
    embed n m (sourceAction ρF ρB n m h p) = action ρF ρB h (embed n m p) := by
  have he : (embed n m).comp (sourceAction (I := I) ρF ρB n m h) =
      (action ρF ρB h).comp (embed n m) := by
    apply MixedPowerDescent.ext n m
    intro v w
    simp only [LinearMap.comp_apply, sourceAction, MixedWeightSupport.pure,
      Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.exteriorPower_apply_ιMulti, Representation.symmetricPower_apply_tprod]
    change embed n m (MixedWeightSupport.pure (fun i => JetLinear.map (ρF h) (v i))
      (fun j => JetLinear.map (ρB h) (w j))) = action ρF ρB h (embed n m (MixedWeightSupport.pure v w))
    rw [embed_pure, embed_pure]
    change _ = ExteriorAlgebra.map (JetLinear.map (ρF h)) (ExteriorAlgebra.ιMulti ℂ n v) ⊗ₜ[ℂ]
      polynomialMap (ρB h) (∏ j, SymmetricPolynomialPower.linearForm (w j))
    rw [ExteriorAlgebra.map_apply_ιMulti, map_prod]
    apply congrArg₂ (fun (x : Odd F I) (y : Even B I) => x ⊗ₜ[ℂ] y)
    · rfl
    · apply Finset.prod_congr rfl
      intro j _
      exact (polynomialMap_linearForm (ρB h) (w j)).symm
  exact LinearMap.congr_fun he p

@[reducible] local instance (n m : ℕ) : AddCommGroup (Source F B I n m) := inferInstance
@[reducible] local instance (n m : ℕ) : Module ℂ (Source F B I n m) := inferInstance
@[reducible] local instance (n m d : ℕ) : AddCommGroup (sourceGrade F B I n m d) := inferInstance
@[reducible] local instance (n m d : ℕ) : Module ℂ (sourceGrade F B I n m d) := inferInstance

instance sourceGrade_finiteDimensional [Finite F] [Finite B] [Finite I] (n m d : ℕ) :
    FiniteDimensional ℂ (sourceGrade F B I n m d) := by
  let e : sourceGrade F B I n m d ≃ₗ[ℂ] grade F B I n m d := gradeEquiv n m d
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

def sourceGradeAction {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (n m d : ℕ) :
    Representation ℂ H (sourceGrade F B I n m d) where
  toFun h :=
    { toFun p := ⟨sourceAction ρF ρB n m h p.val, by
        change embed n m (sourceAction ρF ρB n m h p.val) ∈ grade F B I n m d
        rw [embed_action]
        exact action_mem ρF ρB h p.property⟩
      map_add' _ _ := Subtype.ext (map_add _ _ _)
      map_smul' _ _ := Subtype.ext (map_smul _ _ _) }
  map_one' := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact LinearMap.congr_fun (sourceAction (I := I) ρF ρB n m).map_one p.val
  map_mul' h k := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact LinearMap.congr_fun ((sourceAction (I := I) ρF ρB n m).map_mul h k) p.val

theorem gradeEquiv_action {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (n m d : ℕ) (h : H)
    (p : sourceGrade F B I n m d) :
    gradeEquiv n m d (sourceGradeAction ρF ρB n m d h p) =
      gradeAction ρF ρB n m d h (gradeEquiv n m d p) :=
  Subtype.ext (embed_action ρF ρB n m h p.val)

def gradeRepresentationEquiv {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (n m d : ℕ) :
    Representation.Equiv (sourceGradeAction (I := I) ρF ρB n m d) (gradeAction (I := I) ρF ρB n m d) :=
  Representation.Equiv.mk (gradeEquiv n m d) (by
    intro h
    apply LinearMap.ext
    exact gradeEquiv_action ρF ρB n m d h)

end
end Math.MixedJetSource
