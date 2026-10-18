import Math.RepresentationTheory.TripleFlavorCoordinates

/-! Diagonal weights preserve the nonredundant triple-flavor dictionaries.
These identities include repeated indices and the mixed-symmetry branch. -/
namespace Math.TripleFlavorWeights
set_option autoImplicit false
noncomputable section
variable {n : ℕ}

def symmetricWeight (w : Fin n → ℂ) (p : TripleSymmetricCoordinates.Index n) : ℂ :=
  w p.val.1 * w p.val.2.1 * w p.val.2.2

def alternatingWeight (w : Fin n → ℂ) (p : TripleAlternatingCoordinates.Index n) : ℂ :=
  w p.val.1 * w p.val.2.1 * w p.val.2.2

def mixedWeight (w : Fin n → ℂ) : TripleMixedCoordinates.Index n → ℂ
  | .inl p => w p.val.1 * w p.val.1 * w p.val.2
  | .inr (p, _) => w p.val.1 * w p.val.2.1 * w p.val.2.2

def weight (w : Fin n → ℂ) : TripleFlavorCoordinates.Index n → ℂ
  | .inl p => symmetricWeight w p
  | .inr (.inl p) => alternatingWeight w p
  | .inr (.inr p) => mixedWeight w p

def triple {A : Type*} (q : Fin n → A) : TripleFlavorCoordinates.Index n → A × A × A
  | .inl p => (q p.val.1, q p.val.2.1, q p.val.2.2)
  | .inr (.inl p) => (q p.val.1, q p.val.2.1, q p.val.2.2)
  | .inr (.inr (.inl p)) => (q p.val.1, q p.val.1, q p.val.2)
  | .inr (.inr (.inr (p, _))) => (q p.val.1, q p.val.2.1, q p.val.2.2)

def charge {A : Type*} [Add A] (q : Fin n → A) (p : TripleFlavorCoordinates.Index n) : A :=
  let t := triple q p
  t.1 + t.2.1 + t.2.2

theorem symmetric_assemble (a : ℂ) (w : Fin n → ℂ) (d : TripleSymmetricCoordinates.Coordinates n)
    (x y z : Fin n) :
    TripleSymmetricCoordinates.assemble (fun p => a * symmetricWeight w p * d p) x y z =
      (w x * w y * w z * a) * TripleSymmetricCoordinates.assemble d x y z := by
  unfold TripleSymmetricCoordinates.assemble
  split_ifs <;> simp only [symmetricWeight] <;> ring

theorem alternating_assemble (a : ℂ) (w : Fin n → ℂ) (d : TripleAlternatingCoordinates.Coordinates n)
    (x y z : Fin n) :
    TripleAlternatingCoordinates.assemble (fun p => a * alternatingWeight w p * d p) x y z =
      (w x * w y * w z * a) * TripleAlternatingCoordinates.assemble d x y z := by
  unfold TripleAlternatingCoordinates.assemble
  split_ifs <;> (try simp only [alternatingWeight]) <;> ring

theorem mixed_assemble (a : ℂ) (w : Fin n → ℂ) (d : TripleMixedCoordinates.Coordinates n)
    (x y z : Fin n) :
    TripleMixedCoordinates.assemble (fun p => a * mixedWeight w p * d p) x y z =
      (w x * w y * w z * a) * TripleMixedCoordinates.assemble d x y z := by
  unfold TripleMixedCoordinates.assemble
  split_ifs <;> simp_all only [mixedWeight] <;> ring

end
end Math.TripleFlavorWeights
