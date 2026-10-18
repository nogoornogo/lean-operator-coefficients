import Math.LinearAlgebra.ConstrainedCompleteness

/-! Statistics on a set of generators. The coordinate action is supplied
independently and compatibility is an equality of linear maps, not a premise
that the already constrained spaces happen to be equivalent. -/
namespace Math.StatisticalCompleteness
set_option autoImplicit false
noncomputable section
variable {k J A B : Type*} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]

def sector (action : J → A →ₗ[k] A) (sign : J → k) : Submodule k A where
  carrier := {x | ∀ j, action j x = sign j • x}
  zero_mem' := by intro j; simp
  add_mem' := by intro x y hx hy j; simp [hx j, hy j, smul_add]
  smul_mem' := by intro z x hx j; simp [hx j, smul_smul, mul_comm]

theorem statistics_iff (coordinates : A ≃ₗ[k] B)
    (source : J → A →ₗ[k] A) (target : J → B →ₗ[k] B) (sign : J → k)
    (compatible : ∀ j x, coordinates (source j x) = target j (coordinates x)) (x : A) :
    x ∈ sector source sign ↔ coordinates x ∈ sector target sign := by
  constructor
  · intro hx j
    rw [← compatible, hx j, coordinates.map_smul]
  · intro hx j
    apply coordinates.injective
    rw [compatible, hx j, coordinates.map_smul]

def equiv (coordinates : A ≃ₗ[k] B)
    (source : J → A →ₗ[k] A) (target : J → B →ₗ[k] B) (sign : J → k)
    (compatible : ∀ j x, coordinates (source j x) = target j (coordinates x)) :
    sector source sign ≃ₗ[k] sector target sign :=
  (ConstrainedCompleteness.Presentation.mk coordinates
    (statistics_iff coordinates source target sign compatible)).equiv

/-- Pointwise form for heterogeneous flavor inputs: `y` and `z` may be
coordinates at different, exchanged flavor arguments. -/
theorem relation_iff (reconstruct : B →ₗ[k] A) (injective : Function.Injective reconstruct)
    (source : A → A) (target : B → B)
    (compatible : ∀ y, reconstruct (target y) = source (reconstruct y))
    (sign : k) (y z : B) :
    target y = sign • z ↔ source (reconstruct y) = sign • reconstruct z := by
  constructor
  · intro h
    rw [← compatible, h, reconstruct.map_smul]
  · intro h
    apply injective
    rw [compatible, reconstruct.map_smul, h]

@[simp] theorem equiv_apply (coordinates : A ≃ₗ[k] B)
    (source : J → A →ₗ[k] A) (target : J → B →ₗ[k] B) (sign : J → k)
    (compatible : ∀ j x, coordinates (source j x) = target j (coordinates x))
    (x : sector source sign) :
    (equiv coordinates source target sign compatible x : B) = coordinates x := rfl

/-- With no repeated fields the generator conditions are vacuous, rather
than artificially imposing exterior statistics on an ordered sector. -/
def emptySectorEquiv : sector (k := k) (A := A)
    (fun j : Empty => nomatch j) (fun j => nomatch j) ≃ₗ[k] A where
  toFun x := x.val
  invFun x := ⟨x, fun j => nomatch j⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def noExchanges (coordinates : A ≃ₗ[k] B) : A ≃ₗ[k] B :=
  (emptySectorEquiv (k := k) (A := A)).symm.trans
    ((equiv coordinates (fun j : Empty => nomatch j) (fun j => nomatch j)
      (fun j => nomatch j) (fun j => nomatch j)).trans emptySectorEquiv)

theorem noExchanges_agrees (coordinates : A ≃ₗ[k] B) : noExchanges coordinates = coordinates := by
  apply LinearEquiv.ext
  intro x
  rfl

end
end Math.StatisticalCompleteness
