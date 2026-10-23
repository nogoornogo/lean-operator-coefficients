import Math.RepresentationTheory.Exterior.SymmetricSquareCauchy
import Math.LinearAlgebra.Symmetric.SymmetricPurePowers

/-! Complete symmetric-square splitting of a direct sum, retaining both
arbitrary actions and the mixed tensor component. -/
namespace Math.SymmetricSquareSum
set_option autoImplicit false
noncomputable section
open Representation TensorSquareQuotients
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
abbrev Total := Sym[ℂ]^2 (A × B)
abbrev Pieces := (Sym[ℂ]^2 A) × ((A ⊗[ℂ] B) × (Sym[ℂ]^2 B))
@[reducible] local instance : AddCommGroup (Total (A := A) (B := B)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (Pieces (A := A) (B := B)) :=
  Module.addCommMonoidToAddCommGroup ℂ

theorem sym_map {U V : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] (f : U →ₗ[ℂ] V) (a b : U) :
    SymmetricPower.map (ι := Fin 2) f (sym (a ⊗ₜ[ℂ] b))=sym (f a ⊗ₜ[ℂ] f b) := by
  rw [sym_tmul, sym_tmul, SymmetricPower.map_tprod]
  congr 1
  ext i
  fin_cases i <;> rfl

def first : Total (A := A) (B := B) →ₗ[ℂ] Sym[ℂ]^2 A :=
  SymmetricPower.map (ι := Fin 2) (LinearMap.fst ℂ A B)
def middle : Total (A := A) (B := B) →ₗ[ℂ] (A ⊗[ℂ] B) :=
  (TensorProduct.map (LinearMap.fst ℂ A B) (LinearMap.snd ℂ A B)).comp symmetricSection
def last : Total (A := A) (B := B) →ₗ[ℂ] Sym[ℂ]^2 B :=
  SymmetricPower.map (ι := Fin 2) (LinearMap.snd ℂ A B)

def left : Sym[ℂ]^2 A →ₗ[ℂ] Total (A := A) (B := B) :=
  SymmetricPower.map (ι := Fin 2) (LinearMap.inl ℂ A B)
def mixed : (A ⊗[ℂ] B) →ₗ[ℂ] Total (A := A) (B := B) :=
  sym.comp (TensorProduct.map (LinearMap.inl ℂ A B) (LinearMap.inr ℂ A B))
def right : Sym[ℂ]^2 B →ₗ[ℂ] Total (A := A) (B := B) :=
  SymmetricPower.map (ι := Fin 2) (LinearMap.inr ℂ A B)

theorem first_pure (a c : A) (b d : B) :
    first (sym ((a,b) ⊗ₜ[ℂ] (c,d)))=sym (a ⊗ₜ[ℂ] c) :=
  sym_map (LinearMap.fst ℂ A B) _ _

theorem middle_pure (a c : A) (b d : B) :
    middle (sym ((a,b) ⊗ₜ[ℂ] (c,d)))=a ⊗ₜ[ℂ] d+c ⊗ₜ[ℂ] b := by
  simp only [middle, LinearMap.comp_apply, symmetricSection_pure, map_add, TensorProduct.map_tmul]
  rfl

theorem last_pure (a c : A) (b d : B) :
    last (sym ((a,b) ⊗ₜ[ℂ] (c,d)))=sym (b ⊗ₜ[ℂ] d) :=
  sym_map (LinearMap.snd ℂ A B) _ _

theorem left_pure (a c : A) : left (sym (a ⊗ₜ[ℂ] c))=sym ((a,(0 : B)) ⊗ₜ[ℂ] (c,0)) :=
  sym_map (LinearMap.inl ℂ A B) _ _
theorem right_pure (b d : B) : right (sym (b ⊗ₜ[ℂ] d))=sym (((0 : A),b) ⊗ₜ[ℂ] (0,d)) :=
  sym_map (LinearMap.inr ℂ A B) _ _
theorem mixed_pure (a : A) (b : B) : mixed (a ⊗ₜ[ℂ] b)=sym ((a,(0 : B)) ⊗ₜ[ℂ] ((0 : A),b)) := rfl

def forward : Total (A := A) (B := B) →ₗ[ℂ] Pieces (A := A) (B := B) :=
  first.prod (middle.prod last)
def backward : Pieces (A := A) (B := B) →ₗ[ℂ] Total (A := A) (B := B) :=
  left.coprod (mixed.coprod right)

theorem backward_forward (x : Total (A := A) (B := B)) : backward (forward x)=x := by
  have h : (backward (A := A) (B := B)).comp forward=LinearMap.id := by
    apply SymmetricPower.ext
    intro v
    rw [← sym_eta v]
    change left (first (sym (v 0 ⊗ₜ[ℂ] v 1)))+
      (mixed (middle (sym (v 0 ⊗ₜ[ℂ] v 1)))+right (last (sym (v 0 ⊗ₜ[ℂ] v 1))))=
      sym (v 0 ⊗ₜ[ℂ] v 1)
    rcases v 0 with ⟨a,b⟩
    rcases v 1 with ⟨c,d⟩
    rw [first_pure, middle_pure, last_pure, left_pure, map_add, mixed_pure, mixed_pure, right_pure]
    have h1 : (a,b)=(a,(0 : B))+((0 : A),b) := by simp
    have h2 : (c,d)=(c,(0 : B))+((0 : A),d) := by simp
    conv_rhs => rw [h1, h2, TensorProduct.add_tmul, TensorProduct.tmul_add,
      TensorProduct.tmul_add, map_add, map_add, map_add]
    rw [sym_swap ((0 : A),b) (c,(0 : B))]
    abel
  exact LinearMap.congr_fun h x

theorem forward_left (x : Sym[ℂ]^2 A) : forward (left (B := B) x)=(x,((0 : A ⊗[ℂ] B),(0 : Sym[ℂ]^2 B))) := by
  have h : (forward (A := A) (B := B)).comp left=
      (LinearMap.inl ℂ _ _) := by
    apply SymmetricPower.ext
    intro v
    rw [← sym_eta v]
    change (first (left (sym (v 0 ⊗ₜ[ℂ] v 1))),
      (middle (left (sym (v 0 ⊗ₜ[ℂ] v 1))),last (left (sym (v 0 ⊗ₜ[ℂ] v 1)))))=_
    rw [left_pure, first_pure, middle_pure, last_pure]
    simp only [TensorProduct.tmul_zero, map_zero, add_zero]
    rfl
  exact LinearMap.congr_fun h x

theorem forward_right (x : Sym[ℂ]^2 B) : forward (right x)=((0 : Sym[ℂ]^2 A),(0,x)) := by
  have h : (forward (A := A) (B := B)).comp right=
      (LinearMap.inr ℂ _ _).comp (LinearMap.inr ℂ _ _) := by
    apply SymmetricPower.ext
    intro v
    rw [← sym_eta v]
    change (first (right (sym (v 0 ⊗ₜ[ℂ] v 1))),
      (middle (right (sym (v 0 ⊗ₜ[ℂ] v 1))),last (right (sym (v 0 ⊗ₜ[ℂ] v 1)))))=_
    rw [right_pure, first_pure, middle_pure, last_pure]
    simp only [TensorProduct.tmul_zero, TensorProduct.zero_tmul, map_zero, add_zero]
    rfl
  exact LinearMap.congr_fun h x

theorem forward_mixed (x : A ⊗[ℂ] B) : forward (mixed x)=((0 : Sym[ℂ]^2 A),(x,0)) := by
  have h : (forward (A := A) (B := B)).comp mixed=
      (LinearMap.inr ℂ _ _).comp (LinearMap.inl ℂ _ _) := by
    apply TensorProduct.ext'
    intro a b
    change (first (mixed (a ⊗ₜ[ℂ] b)),(middle (mixed (a ⊗ₜ[ℂ] b)),last (mixed (a ⊗ₜ[ℂ] b))))=_
    rw [mixed_pure, first_pure, middle_pure, last_pure]
    simp only [TensorProduct.tmul_zero, TensorProduct.zero_tmul, map_zero, add_zero]
    rfl
  exact LinearMap.congr_fun h x

def linearEquivalence : Total (A := A) (B := B) ≃ₗ[ℂ] Pieces (A := A) (B := B) where
  toLinearMap := forward
  invFun := backward
  left_inv := backward_forward
  right_inv x := by
    change forward (left x.1+(mixed x.2.1+right x.2.2))=x
    rw [map_add, map_add, forward_left, forward_mixed, forward_right]
    apply Prod.ext
    · simp
    · apply Prod.ext <;> simp

variable {G : Type*} [Group G] (r : Representation ℂ G A) (s : Representation ℂ G B)

def equivalence : Representation.Equiv ((r.prod s).symmetricPower 2)
    ((r.symmetricPower 2).prod ((r.tprod s).prod (s.symmetricPower 2))) where
  toLinearEquiv := linearEquivalence
  isIntertwining' g := by
    apply SymmetricPower.ext
    intro v
    rw [← sym_eta v]
    rcases v 0 with ⟨a,b⟩
    rcases v 1 with ⟨c,d⟩
    change forward (SymmetricPower.map (ι := Fin 2) ((r.prod s) g) (sym ((a,b) ⊗ₜ[ℂ] (c,d))))=_
    rw [← SymmetricSquareCauchyRepresentation.sym_natural]
    change (first (sym ((r g a,s g b) ⊗ₜ[ℂ] (r g c,s g d))),
      (middle (sym ((r g a,s g b) ⊗ₜ[ℂ] (r g c,s g d))),
        last (sym ((r g a,s g b) ⊗ₜ[ℂ] (r g c,s g d)))))=_
    rw [first_pure, middle_pure, last_pure]
    change _=((r.symmetricPower 2) g (first (sym ((a,b) ⊗ₜ[ℂ] (c,d)))),
      ((r.tprod s) g (middle (sym ((a,b) ⊗ₜ[ℂ] (c,d)))),
        (s.symmetricPower 2) g (last (sym ((a,b) ⊗ₜ[ℂ] (c,d))))))
    rw [first_pure, middle_pure, last_pure,
      SymmetricSquareCauchyRepresentation.sym_natural,
      SymmetricSquareCauchyRepresentation.sym_natural, map_add]
    rfl

end
end Math.SymmetricSquareSum
