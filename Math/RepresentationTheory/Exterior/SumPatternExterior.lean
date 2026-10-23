import Math.LinearAlgebra.Exterior.BinaryExteriorProduct
import Math.RepresentationTheory.Exterior.PatternExteriorSource

/-! The induction step separates two entire species families, with selected statistics. -/
namespace Math.SumPatternExterior
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
universe u
variable {S T G : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T] [Group G]
  {V : S → Type u} {W : T → Type u}
  [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  [∀ t, AddCommGroup (W t)] [∀ t, Module ℂ (W t)]

abbrev Fields (a : S ⊕ T) : Type _ := match a with | .inl s => V s | .inr t => W t
instance (a : S ⊕ T) : AddCommGroup (Fields (V := V) (W := W) a) := match a with | .inl _ => inferInstance | .inr _ => inferInstance
instance (a : S ⊕ T) : Module ℂ (Fields (V := V) (W := W) a) := match a with | .inl _ => inferInstance | .inr _ => inferInstance

def join : ((∀ s, V s) × (∀ t, W t)) ≃ₗ[ℂ] (∀ a, Fields (V := V) (W := W) a) where
  toFun x a := match a with | .inl s => x.1 s | .inr t => x.2 t
  invFun x := (fun s => x (.inl s),fun t => x (.inr t))
  left_inv _ := rfl
  right_inv x := by funext a; cases a <;> rfl
  map_add' _ _ := by funext a; cases a <;> rfl
  map_smul' _ _ := by funext a; cases a <;> rfl

variable (r : ∀ s, Representation ℂ G (V s)) (t : ∀ a, Representation ℂ G (W a))
  {n m : ℕ} (p : Fin n → S) (q : Fin m → T)

def fields : ∀ a, Representation ℂ G (Fields (V := V) (W := W) a) := fun a => match a with | .inl s => r s | .inr a => t a
def pattern : Fin (n+m) → S ⊕ T := Fin.append (Sum.inl ∘ p) (Sum.inr ∘ q)

def raw : (PatternExteriorSource.Source r p) ⊗[ℂ] (PatternExteriorSource.Source t q) →ₗ[ℂ]
    ⋀[ℂ]^(n+m) (∀ a, Fields (V := V) (W := W) a) :=
  (exteriorPower.map (n+m) (join (V := V) (W := W)).toLinearMap).comp
    ((BinaryExteriorProduct.map n m).comp
      (TensorProduct.map (PatternExteriorSource.Source r p).subtype (PatternExteriorSource.Source t q).subtype))

theorem raw_injective : Function.Injective (raw r t p q) :=
  (exteriorPower.map_injective_field (n := n+m) (join (V := V) (W := W)).injective).comp
    ((BinaryExteriorProduct.injective n m).comp
      (TensorProduct.map_injective_of_flat_flat _ _
        (Submodule.injective_subtype _) (Submodule.injective_subtype _)))

def vectors (v : ∀ i, V (p i)) (w : ∀ j, W (q j)) :
    Fin (n+m) → ∀ a, Fields (V := V) (W := W) a :=
  Fin.append (fun i => Pi.single (Sum.inl (p i)) (v i))
    (fun j => Pi.single (Sum.inr (q j)) (w j))
def values (v : ∀ i, V (p i)) (w : ∀ j, W (q j)) : ∀ i, Fields (V := V) (W := W) (pattern p q i) :=
  fun i => vectors p q v w i (pattern p q i)

private theorem single_project {A : Type*} [DecidableEq A] {F : A → Type*} [∀ a, AddCommGroup (F a)]
    {a b : A} (h : a = b) (x : F b) : Pi.single a (Pi.single b x a) = Pi.single b x := by
  subst a; simp

theorem raw_pure (v : ∀ i, V (p i)) (w : ∀ j, W (q j)) :
    raw r t p q (PatternExteriorSource.pure r p v ⊗ₜ[ℂ] PatternExteriorSource.pure t q w) =
      (PatternExteriorSource.pure (fields r t) (pattern p q) (values p q v w)).val := by
  simp only [raw,LinearMap.comp_apply,TensorProduct.map_tmul,Submodule.subtype_apply,
    PatternExteriorSource.pure_val]
  rw [BinaryExteriorProduct.map_pure,exteriorPower.map_apply_ιMulti]
  apply congrArg (exteriorPower.ιMulti ℂ (n+m))
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Function.comp_apply,Fin.append_left,values,vectors]
    have hj : join (V := V) (W := W) (Pi.single (p j) (v j),0) = Pi.single (Sum.inl (p j)) (v j) := by
      funext a; cases a <;> simp [join,Pi.single]
      rfl
    change join (V := V) (W := W) (Pi.single (p j) (v j),0) = _
    rw [hj]
    exact (single_project (F := Fields (V := V) (W := W)) (Fin.append_left (Sum.inl ∘ p) (Sum.inr ∘ q) j) (v j)).symm
  · intro j
    simp only [Function.comp_apply,Fin.append_right,values,vectors]
    have hj : join (V := V) (W := W) (0,Pi.single (q j) (w j)) = Pi.single (Sum.inr (q j)) (w j) := by
      funext a; cases a <;> simp [join,Pi.single]
      rfl
    change join (V := V) (W := W) (0,Pi.single (q j) (w j)) = _
    rw [hj]
    exact (single_project (F := Fields (V := V) (W := W)) (Fin.append_right (Sum.inl ∘ p) (Sum.inr ∘ q) j) (w j)).symm

theorem tensor_ext {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {f g : PatternExteriorSource.Source r p ⊗[ℂ] PatternExteriorSource.Source t q →ₗ[ℂ] Y}
    (h : ∀ v w, f (PatternExteriorSource.pure r p v ⊗ₜ[ℂ] PatternExteriorSource.pure t q w) =
      g (PatternExteriorSource.pure r p v ⊗ₜ[ℂ] PatternExteriorSource.pure t q w)) : f = g := by
  apply TensorProduct.ext'
  intro x y
  have hx : f.comp ((TensorProduct.mk ℂ _ _).flip y) = g.comp ((TensorProduct.mk ℂ _ _).flip y) := by
    apply LinearMap.ext
    intro x
    obtain ⟨z,rfl⟩ := PatternExteriorSource.onto_surjective r p x
    have he : (f.comp ((TensorProduct.mk ℂ _ _).flip y)).comp (PatternExteriorSource.onto r p).toLinearMap =
        (g.comp ((TensorProduct.mk ℂ _ _).flip y)).comp (PatternExteriorSource.onto r p).toLinearMap := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro v
      have hy : f.comp (TensorProduct.mk ℂ _ _ (PatternExteriorSource.pure r p v)) =
          g.comp (TensorProduct.mk ℂ _ _ (PatternExteriorSource.pure r p v)) := by
        apply LinearMap.ext
        intro y
        obtain ⟨w,rfl⟩ := PatternExteriorSource.onto_surjective t q y
        have hh : (f.comp (TensorProduct.mk ℂ _ _ (PatternExteriorSource.pure r p v))).comp
            (PatternExteriorSource.onto t q).toLinearMap =
            (g.comp (TensorProduct.mk ℂ _ _ (PatternExteriorSource.pure r p v))).comp
            (PatternExteriorSource.onto t q).toLinearMap := by
          apply PiTensorProduct.ext
          apply MultilinearMap.ext
          intro w
          exact h v w
        exact LinearMap.congr_fun hh w
      exact LinearMap.congr_fun hy y
    exact LinearMap.congr_fun he z
  exact LinearMap.congr_fun hx x

def forward : PatternExteriorSource.Source r p ⊗[ℂ] PatternExteriorSource.Source t q →ₗ[ℂ]
    PatternExteriorSource.Source (fields r t) (pattern p q) :=
  (PatternExteriorSource.projectionLinear (fields r t) (pattern p q)).comp (raw r t p q)

theorem forward_pure (v : ∀ i, V (p i)) (w : ∀ j, W (q j)) :
    forward r t p q (PatternExteriorSource.pure r p v ⊗ₜ[ℂ] PatternExteriorSource.pure t q w) =
      PatternExteriorSource.pure (fields r t) (pattern p q) (values p q v w) := by
  rw [forward,LinearMap.comp_apply,raw_pure]
  exact PatternExteriorSource.projection_inclusion _ _ _

theorem inclusion_forward : (PatternExteriorSource.Source (fields r t) (pattern p q)).subtype.comp
    (forward r t p q) = raw r t p q := by
  apply tensor_ext r t p q
  intro v w
  change (forward r t p q (_ ⊗ₜ[ℂ] _)).val = _
  rw [forward_pure,raw_pure]

theorem forward_injective : Function.Injective (forward r t p q) := by
  intro x y h
  apply raw_injective r t p q
  exact (LinearMap.congr_fun (inclusion_forward r t p q) x).symm.trans
    ((congrArg Subtype.val h).trans (LinearMap.congr_fun (inclusion_forward r t p q) y))

def leftValues (v : ∀ i, Fields (V := V) (W := W) (pattern p q i)) : ∀ i, V (p i) := fun j =>
  cast (congrArg (Fields (V := V) (W := W)) (Fin.append_left (Sum.inl ∘ p) (Sum.inr ∘ q) j))
    (v (Fin.castAdd m j))
def rightValues (v : ∀ i, Fields (V := V) (W := W) (pattern p q i)) : ∀ j, W (q j) := fun j =>
  cast (congrArg (Fields (V := V) (W := W)) (Fin.append_right (Sum.inl ∘ p) (Sum.inr ∘ q) j))
    (v (Fin.natAdd n j))

private theorem single_cast {A : Type*} [DecidableEq A] {F : A → Type*} [∀ a, AddCommGroup (F a)]
    {a b : A} (h : a = b) (x : F a) : Pi.single b (cast (congrArg F h) x) a = x := by
  subst b; simp

omit [Fintype S] [Fintype T] [∀ s, Module ℂ (V s)] [∀ t, Module ℂ (W t)] in
theorem values_reconstruct (v : ∀ i, Fields (V := V) (W := W) (pattern p q i)) :
    values p q (leftValues p q v) (rightValues p q v) = v := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [values,vectors,leftValues,Fin.append_left]
    exact single_cast (Fin.append_left (Sum.inl ∘ p) (Sum.inr ∘ q) j) (v (Fin.castAdd m j))
  · intro j
    simp only [values,vectors,rightValues,Fin.append_right]
    exact single_cast (Fin.append_right (Sum.inl ∘ p) (Sum.inr ∘ q) j) (v (Fin.natAdd n j))

theorem forward_surjective : Function.Surjective (forward r t p q) := by
  have h : LinearMap.range (PatternExteriorSource.onto (fields r t) (pattern p q)).toLinearMap ≤
      LinearMap.range (forward r t p q) := by
    rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top,
      Submodule.map_span,Submodule.span_le]
    rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    refine ⟨PatternExteriorSource.pure r p (leftValues p q v) ⊗ₜ[ℂ]
      PatternExteriorSource.pure t q (rightValues p q v), ?_⟩
    rw [forward_pure,values_reconstruct]
    rfl
  have ht := LinearMap.range_eq_top.mpr (PatternExteriorSource.onto_surjective (fields r t) (pattern p q))
  exact LinearMap.range_eq_top.mp (top_le_iff.mp (ht ▸ h))

def linearEquiv : PatternExteriorSource.Source r p ⊗[ℂ] PatternExteriorSource.Source t q ≃ₗ[ℂ]
    PatternExteriorSource.Source (fields r t) (pattern p q) :=
  LinearEquiv.ofBijective (forward r t p q) ⟨forward_injective r t p q,forward_surjective r t p q⟩

private theorem single_action {A B : Type*} [DecidableEq A] [Group B]
    {F : A → Type*} [∀ a, AddCommGroup (F a)] [∀ a, Module ℂ (F a)]
    (r : ∀ a, Representation ℂ B (F a)) {a b : A} (h : a = b) (g : B) (x : F b) :
    r a g (Pi.single b x a) = Pi.single b (r b g x) a := by
  subst a; simp

omit [Fintype S] [Fintype T] in
theorem values_action (g : G) (v : ∀ i, V (p i)) (w : ∀ j, W (q j)) :
    values p q (fun i => r (p i) g (v i)) (fun j => t (q j) g (w j)) =
      fun i => fields r t (pattern p q i) g (values p q v w i) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [values,vectors,Fin.append_left]
    exact (single_action (fields r t) (Fin.append_left (Sum.inl ∘ p) (Sum.inr ∘ q) j) g (v j)).symm
  · intro j
    simp only [values,vectors,Fin.append_right]
    exact (single_action (fields r t) (Fin.append_right (Sum.inl ∘ p) (Sum.inr ∘ q) j) g (w j)).symm

def equiv : Representation.Equiv
    ((PatternExteriorSource.representation r p).tprod (PatternExteriorSource.representation t q))
    (PatternExteriorSource.representation (fields r t) (pattern p q)) where
  toLinearEquiv := linearEquiv r t p q
  isIntertwining' g := by
    apply tensor_ext r t p q
    intro v w
    simp only [LinearMap.comp_apply,Representation.tprod_apply,TensorProduct.map_tmul]
    change forward r t p q ((PatternExteriorSource.representation r p g (PatternExteriorSource.pure r p v)) ⊗ₜ[ℂ]
      (PatternExteriorSource.representation t q g (PatternExteriorSource.pure t q w))) =
      PatternExteriorSource.representation (fields r t) (pattern p q) g (forward r t p q (_ ⊗ₜ[ℂ] _))
    rw [← PatternExteriorSource.pure_action r p g v, ← PatternExteriorSource.pure_action t q g w,
      forward_pure,forward_pure,← PatternExteriorSource.pure_action]
    exact congrArg (PatternExteriorSource.pure (fields r t) (pattern p q)) (values_action r t p q g v w)

end
end Math.SumPatternExterior
