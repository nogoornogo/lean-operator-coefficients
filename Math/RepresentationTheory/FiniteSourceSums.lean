import Math.RepresentationTheory.FiniteExternalProducts

/-! Singleton and disjoint-union presentation of finite representation sums.
These actual equivalences also apply to reducible, zero and repeated blocks. -/
namespace Math.FiniteSourceSums
set_option autoImplicit false
noncomputable section
open Representation
universe u

variable {G I J V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  {A : I → Type u} {B : J → Type u}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)]

def singleton (rho : Representation ℂ G V) : Representation.Equiv rho
    (FiniteBlockHom.action (fun _ : Unit => rho)) where
  toLinearEquiv :=
    { toFun := fun x _ => x
      invFun := fun x => x ()
      left_inv _ := rfl
      right_inv x := funext (fun i => congrArg x (Subsingleton.elim () i))
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

def SumCarrier : I ⊕ J → Type u
  | .inl i => A i
  | .inr j => B j

instance sumAdditive : (p : I ⊕ J) → AddCommGroup (SumCarrier (A := A) (B := B) p)
  | .inl i => inferInstanceAs (AddCommGroup (A i))
  | .inr j => inferInstanceAs (AddCommGroup (B j))
instance sumLinear : (p : I ⊕ J) → Module ℂ (SumCarrier (A := A) (B := B) p)
  | .inl i => inferInstanceAs (Module ℂ (A i))
  | .inr j => inferInstanceAs (Module ℂ (B j))

def sumAction (a : ∀ i, Representation ℂ G (A i)) (b : ∀ j, Representation ℂ G (B j)) :
    (p : I ⊕ J) → Representation ℂ G (SumCarrier (A := A) (B := B) p)
  | .inl i => a i
  | .inr j => b j

def sumEquivalence (a : ∀ i, Representation ℂ G (A i)) (b : ∀ j, Representation ℂ G (B j)) :
    Representation.Equiv ((FiniteBlockHom.action a).prod (FiniteBlockHom.action b))
      (FiniteBlockHom.action (sumAction a b)) where
  toLinearEquiv :=
    { toFun := fun x p => match p with | .inl i => x.1 i | .inr j => x.2 j
      invFun := fun x => (fun i => x (.inl i),fun j => x (.inr j))
      left_inv _ := rfl
      right_inv x := by funext p; cases p <;> rfl
      map_add' _ _ := by funext p; cases p <;> rfl
      map_smul' _ _ := by funext p; cases p <;> rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext p
    cases p <;> rfl

def finTwoInverse {T : Fin 2 → Type u} (x : T 0 × T 1) : ∀ i, T i :=
  Fin.cases x.1 (Fin.cases x.2 (fun i => Fin.elim0 i))

def finTwo {T : Fin 2 → Type u} [∀ i, AddCommGroup (T i)] [∀ i, Module ℂ (T i)]
    (r : ∀ i, Representation ℂ G (T i)) :
    Representation.Equiv (FiniteBlockHom.action r) ((r 0).prod (r 1)) where
  toLinearEquiv :=
    { toFun := fun x => (x 0,x 1)
      invFun := finTwoInverse
      left_inv x := by funext i; fin_cases i <;> rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

end
end Math.FiniteSourceSums
