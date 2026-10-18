import Math.RepresentationTheory.SU2DoubletTorusSplit
import Math.RepresentationTheory.SU2WeightSlice

/-! Every exterior power of a doublet tensor A has actual weight-(p-q)
space Lambda^p A tensor Lambda^q A at total degree p+q. All actions on A
are retained. This is a source equivalence, not a character identity. -/
namespace Math.SU2ExteriorWeightSlice
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor WeakDoubletScalars TorusWeightSlice
open SU2DoubletTorusSplit
open scoped TensorProduct
variable {K A : Type*} [Group K] [AddCommGroup A] [Module ℂ A]
  (s : Representation ℂ K A)
@[reducible] local instance : AddCommGroup (Doublet ⊗[ℂ] A) :=
  inferInstance
@[reducible] local instance (p q : ℕ) : AddCommGroup
    ((⋀[ℂ]^p A) ⊗[ℂ] (⋀[ℂ]^q A)) := Module.addCommMonoidToAddCommGroup ℂ

abbrev whole (n : ℕ) := (external doublet s).exteriorPower n
abbrev circleWhole (n : ℕ) := (SU2DoubletTorusSplit.source s).exteriorPower n

def restrictWeight (n : ℕ) (k : ℤ) : Representation.Equiv
    (action (whole s n) TauCeti.SU2.torusHom k)
    (action (circleWhole s n) (MonoidHom.id Circle) k) where
  toLinearEquiv :=
    { toFun x := ⟨x.val, x.property⟩
      invFun x := ⟨x.val, x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change whole s n (1,g) x.val=whole s n (TauCeti.SU2.torusHom 1,g) x.val
    rw [map_one]

def residualExterior (i : Fin 2) (p : ℕ) : Representation.Equiv
    (residual ((fields s i).exteriorPower p)) (s.exteriorPower p) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change (fields s i).exteriorPower p (1,g) (exteriorPower.ιMulti ℂ p v)=
      s.exteriorPower p g (exteriorPower.ιMulti ℂ p v)
    rw [Representation.exteriorPower_apply_ιMulti, Representation.exteriorPower_apply_ιMulti]
    apply congrArg (exteriorPower.ιMulti ℂ p)
    funext i
    change fields s _ (1,g) (v i)=s g (v i)
    rw [fields_apply]
    simp

def residualTensor (p q : ℕ) : Representation.Equiv
    (residual (((fields s 0).exteriorPower p).tprod ((fields s 1).exteriorPower q)))
    ((s.exteriorPower p).tprod (s.exteriorPower q)) where
  toLinearEquiv := TensorProduct.congr (residualExterior s 0 p).toLinearEquiv
    (residualExterior s 1 q).toLinearEquiv
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    exact congrArg₂ (fun x y => x ⊗ₜ[ℂ] y)
      ((residualExterior s 0 p).isIntertwining _ _ g x)
      ((residualExterior s 1 q).isIntertwining _ _ g y)

/-- Uniform actual exterior-weight equivalence, independent of the
dimension or irreducible decomposition of the retained representation. -/
def equivalence (p q : ℕ) : Representation.Equiv
    (action (whole s (p+q)) TauCeti.SU2.torusHom ((p : ℤ)-q))
    ((s.exteriorPower p).tprod (s.exteriorPower q)) :=
  (restrictWeight s (p+q) _).trans
  ((transport (circleWhole s (p+q)) (MonoidHom.id Circle)
    ((SU2DoubletTorusSplit.equivalence s).exteriorPower (p+q)) _).trans
  ((BinaryScalarExteriorSlice.equivalence (fields s) (MonoidHom.id Circle)
    (fields_scalar s) p q).trans (residualTensor s p q)))

theorem absent_zero (n : ℕ) (k : ℤ)
    (hk : ¬∃ p q : ℕ, p+q=n ∧ (p : ℤ)-q=k)
    (x : Space (whole s n) TauCeti.SU2.torusHom k) : x=0 := by
  let e := (restrictWeight s n k).trans
    (transport (circleWhole s n) (MonoidHom.id Circle)
      ((SU2DoubletTorusSplit.equivalence s).exteriorPower n) k)
  apply e.injective
  rw [map_zero]
  exact BinaryScalarExteriorSlice.absent_zero (fields s) (MonoidHom.id Circle)
    (fields_scalar s) n k hk (e x)

theorem outside_string (n : ℕ) (k : ℤ) (hk : ¬SU2WeightSlice.InString n k)
    (x : Space (whole s n) TauCeti.SU2.torusHom k) : x=0 := by
  apply absent_zero s n k _ x
  rintro ⟨p,q,hpq,hk'⟩
  apply hk
  dsimp [SU2WeightSlice.InString]
  omega

end
end Math.SU2ExteriorWeightSlice
