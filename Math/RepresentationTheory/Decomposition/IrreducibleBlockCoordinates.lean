import Math.RepresentationTheory.Decomposition.IrreducibleHomScalar

namespace Math.IrreducibleBlockCoordinates
set_option autoImplicit false
noncomputable section
open Representation FiniteBlockHom
variable {G I J : Type*} [Group G] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]
  {A : I → Type*} {B : J → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, FiniteDimensional ℂ (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)]
  (a : ∀ i, Representation ℂ G (A i)) (b : ∀ j, Representation ℂ G (B j))
  [∀ i, IsIrreducible (a i)] [∀ j, IsIrreducible (b j)]

abbrev Match := {p : J × I // Nonempty (Representation.Equiv (a p.2) (b p.1))}
instance : Fintype (Match a b) := Fintype.ofFinite _

def bridge (p : Match a b) : Representation.Equiv (a p.val.2) (b p.val.1) := Classical.choice p.property

def decode (c : Match a b → ℂ) : ∀ j i, IntertwiningMap (a i) (b j) := by
  classical
  exact fun j i => if h : Nonempty (Representation.Equiv (a i) (b j)) then
    IrreducibleHomScalar.equiv (a i) (b j) (bridge a b ⟨(j,i),h⟩) (c ⟨(j,i),h⟩) else 0

def encode (m : ∀ j i, IntertwiningMap (a i) (b j)) : Match a b → ℂ := fun p =>
  (IrreducibleHomScalar.equiv (a p.val.2) (b p.val.1) (bridge a b p)).symm (m p.val.1 p.val.2)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem decode_encode (m : ∀ j i, IntertwiningMap (a i) (b j)) :
    decode a b (encode a b m) = m := by
  classical
  funext j i
  by_cases h : Nonempty (Representation.Equiv (a i) (b j))
  · simp [decode,encode,h]
  · simp [decode,h,IrreducibleHomScalar.unmatched_zero (a i) (b j) h (m j i)]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [∀ j, IsIrreducible (b j)] in
theorem encode_decode (c : Match a b → ℂ) : encode a b (decode a b c) = c := by
  classical
  funext p
  simp [encode,decode,p.property]

def blockEquiv : (∀ j i, IntertwiningMap (a i) (b j)) ≃ₗ[ℂ] (Match a b → ℂ) where
  toFun := encode a b
  invFun := decode a b
  left_inv := decode_encode a b
  right_inv := encode_decode a b
  map_add' x y := by
    funext p
    exact map_add (IrreducibleHomScalar.equiv _ _ (bridge a b p)).symm _ _
  map_smul' z x := by
    funext p
    exact map_smul (IrreducibleHomScalar.equiv _ _ (bridge a b p)).symm z _

def equiv : IntertwiningMap (action a) (action b) ≃ₗ[ℂ] (Match a b → ℂ) :=
  (FiniteBlockHom.equiv a b).trans (blockEquiv a b)

def matrixUnit (p : Match a b) : IntertwiningMap (action a) (action b) := by
  classical
  exact (equiv a b).symm (Pi.single p 1)

/-- These actual intertwiners span without a supplied Hom-basis premise. -/
theorem expansion (f : IntertwiningMap (action a) (action b)) :
    f = ∑ p : Match a b, (equiv a b f p) • matrixUnit a b p := by
  classical
  have he : (equiv a b f) = ∑ p : Match a b, (equiv a b f p) • Pi.single p 1 := by
    ext t; simp [Pi.single_apply]
  apply (equiv a b).injective
  simp only [map_sum,map_smul,matrixUnit,LinearEquiv.apply_symm_apply]
  exact he
end
end Math.IrreducibleBlockCoordinates
