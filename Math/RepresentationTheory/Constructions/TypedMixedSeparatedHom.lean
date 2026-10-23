import Math.RepresentationTheory.Relations.TypedMixedLocalHom
import Math.RepresentationTheory.Tensors.MixedTensorSeparation
import Math.RepresentationTheory.Relations.LocalRelationTensorHom

/-! Field-content residual carriers with separated local and multiplicity tensors. -/
namespace Math.TypedMixedSeparatedHom
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {P Q G H : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Group H]
  {L M : P → Type*} {K N : Q → Type*}
  [∀ u, AddCommGroup (L u)] [∀ u, Module ℂ (L u)]
  [∀ u, AddCommGroup (M u)] [∀ u, Module ℂ (M u)]
  [∀ u, AddCommGroup (K u)] [∀ u, Module ℂ (K u)]
  [∀ u, AddCommGroup (N u)] [∀ u, Module ℂ (N u)]
  (a : ∀ u, Representation ℂ G (L u)) (b : ∀ u, Representation ℂ G (K u))
  (c : ∀ u, Representation ℂ H (M u)) (d : ∀ u, Representation ℂ H (N u))
  {n m : ℕ} (p : Fin n → P) (s : Fin m → Q)

def localF (u : P) := (a u).tprod (trivial ℂ G (M u))
def localB (u : Q) := (b u).tprod (trivial ℂ G (N u))
def residualF (u : P) := (trivial ℂ H (L u)).tprod (c u)
def residualB (u : Q) := (trivial ℂ H (K u)).tprod (d u)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem commutesF : ∀ u g h v, localF (M := M) a u g (residualF (L := L) c u h v) =
    residualF (L := L) c u h (localF (M := M) a u g v) := by
  intro u g h v
  exact LocalCoinvariantTensor.commutes (a u) (c u) g h v
omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem commutesB : ∀ u g h v, localB (N := N) b u g (residualB (K := K) d u h v) =
    residualB (K := K) d u h (localB (N := N) b u g v) := by
  intro u g h v
  exact LocalCoinvariantTensor.commutes (b u) (d u) g h v

abbrev localOrdered := TypedMixedExchangeQuotient.action a b p s
abbrev multiplicityOrdered := TypedMixedExchangeQuotient.action c d p s

def localEquiv : Representation.Equiv
    (TypedMixedExchangeQuotient.action (localF (M := M) a) (localB (N := N) b) p s)
    (LocalCoinvariantTensor.action
      (M := MixedTensorSeparation.Multiplicity (B := fun i => M (p i)) (D := fun j => N (s j)))
      (localOrdered a b p s)) where
  toLinearEquiv := MixedTensorSeparation.equiv
  isIntertwining' g := by
    simpa only [localF, localB, TypedMixedExchangeQuotient.action,
      MultilinearInvariantHom.tensorRepresentation_trivial, MixedTensorSeparation.trivialTensor,
      LocalCoinvariantTensor.action,
      MixedTensorSeparation.representationEquiv_toLinearMap] using
      (MixedTensorSeparation.representationEquiv (fun i => a (p i))
        (fun i => trivial ℂ G (M (p i))) (fun j => b (s j))
        (fun j => trivial ℂ G (N (s j)))).isIntertwining' g

def residualEquiv : Representation.Equiv
    (TypedMixedExchangeQuotient.action (residualF (L := L) c) (residualB (K := K) d) p s)
    (LocalCoinvariantTensor.residual
      (L := MixedTensorSeparation.Local (A := fun i => L (p i)) (C := fun j => K (s j)))
      (multiplicityOrdered c d p s)) where
  toLinearEquiv := MixedTensorSeparation.equiv
  isIntertwining' h := by
    simpa only [residualF, residualB, TypedMixedExchangeQuotient.action,
      MultilinearInvariantHom.tensorRepresentation_trivial, MixedTensorSeparation.trivialTensor,
      LocalCoinvariantTensor.residual,
      MixedTensorSeparation.representationEquiv_toLinearMap] using
      (MixedTensorSeparation.representationEquiv (fun i => trivial ℂ H (L (p i)))
        (fun i => c (p i)) (fun j => trivial ℂ H (K (s j)))
        (fun j => d (s j))).isIntertwining' h

abbrev LocalCarrier := MixedTensorSeparation.Local
  (A := fun i => L (p i)) (C := fun j => K (s j))
abbrev MultiplicityCarrier := MixedTensorSeparation.Multiplicity
  (B := fun i => M (p i)) (D := fun j => N (s j))
abbrev PairedCarrier := TypedMixedExchangeQuotient.Domain
  (V := fun u => L u ⊗[ℂ] M u) (W := fun u => K u ⊗[ℂ] N u) p s

def exchangeRelations : Submodule ℂ
    (LocalCarrier (L := L) (K := K) p s ⊗[ℂ] MultiplicityCarrier (M := M) (N := N) p s) :=
  (TypedMixedExchangeQuotient.relations
  (V := fun u => L u ⊗[ℂ] M u) (W := fun u => K u ⊗[ℂ] N u) p s).map
    (residualEquiv c d p s).toLinearMap

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem exchange_stable : ∀ h, exchangeRelations c d p s ≤
    (exchangeRelations c d p s).comap (LocalCoinvariantTensor.residual
      (L := MixedTensorSeparation.Local (A := fun i => L (p i)) (C := fun j => K (s j)))
      (multiplicityOrdered c d p s) h) :=
  RelationQuotient.map_stable (k := ℂ)
    (U := PairedCarrier (L := L) (M := M) (K := K) (N := N) p s)
    (U' := LocalCarrier (L := L) (K := K) p s ⊗[ℂ] MultiplicityCarrier (M := M) (N := N) p s)
    (TypedMixedExchangeQuotient.action (residualF (L := L) c) (residualB (K := K) d) p s)
    (TypedMixedExchangeQuotient.relations p s)
    (TypedMixedExchangeQuotient.stable (residualF (L := L) c) (residualB (K := K) d) p s)
    (residualEquiv c d p s)

abbrev residual := LocalRelationTensorHom.residual (k := ℂ) (localOrdered a b p s)
  (multiplicityOrdered c d p s) (exchangeRelations c d p s) (exchange_stable c d p s)

abbrev Carrier := LocalRelationTensorHom.Carrier (k := ℂ) (localOrdered a b p s)
  (multiplicityOrdered c d p s) (exchangeRelations c d p s)

def fieldF := TypedMixedLocalHom.fermion (localF (M := M) a) (residualF (L := L) c) (commutesF a c)
def fieldB := TypedMixedLocalHom.boson (localB (N := N) b) (residualB (K := K) d) (commutesB b d)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem local_compatible (g : G)
    (u : PairedCarrier (L := L) (M := M) (K := K) (N := N) p s) :
    residualEquiv c d p s (TypedMixedExchangeQuotient.action
      (localF (M := M) a) (localB (N := N) b) p s g u) =
      LocalCoinvariantTensor.action (M := MultiplicityCarrier (M := M) (N := N) p s)
        (localOrdered a b p s) g (residualEquiv c d p s u) :=
  IntertwiningMap.isIntertwining _ _ (localEquiv a b p s).toIntertwiningMap g u

def separateInputEquiv : LocalRelationHom.Input (k := ℂ)
    (U := PairedCarrier (L := L) (M := M) (K := K) (N := N) p s)
    (TypedMixedExchangeQuotient.action (localF (M := M) a) (localB (N := N) b) p s)
    (TypedMixedExchangeQuotient.action (residualF (L := L) c) (residualB (K := K) d) p s)
    (trivial ℂ H ℂ) (TypedMixedExchangeQuotient.relations p s) ≃ₗ[ℂ]
    LocalRelationHom.Input (k := ℂ)
      (U := LocalCarrier (L := L) (K := K) p s ⊗[ℂ] MultiplicityCarrier (M := M) (N := N) p s)
      (LocalCoinvariantTensor.action (M := MultiplicityCarrier (M := M) (N := N) p s)
        (localOrdered a b p s))
      (LocalCoinvariantTensor.residual (L := LocalCarrier (L := L) (K := K) p s)
        (multiplicityOrdered c d p s)) (trivial ℂ H ℂ) (exchangeRelations c d p s) :=
  LocalRelationHom.alongEquiv (k := ℂ)
    (U := PairedCarrier (L := L) (M := M) (K := K) (N := N) p s)
    (U' := LocalCarrier (L := L) (K := K) p s ⊗[ℂ] MultiplicityCarrier (M := M) (N := N) p s)
    (TypedMixedExchangeQuotient.action (localF (M := M) a) (localB (N := N) b) p s)
    (TypedMixedExchangeQuotient.action (residualF (L := L) c) (residualB (K := K) d) p s)
    (trivial ℂ H ℂ) (TypedMixedExchangeQuotient.relations p s)
    (LocalCoinvariantTensor.action (localOrdered a b p s)) (residualEquiv c d p s)
    (local_compatible a b c d p s)

def equiv : MixedPatternAssembly.orderedSpace (fieldF a c) (fieldB b d) p s ≃ₗ[ℂ]
    IntertwiningMap (residual a b c d p s) (trivial ℂ H ℂ) :=
  (TypedMixedLocalHom.inputEquiv (localF (M := M) a) (localB (N := N) b)
    (residualF (L := L) c) (residualB (K := K) d) (commutesF a c) (commutesB b d) p s).trans
    ((separateInputEquiv a b c d p s).trans
      (LocalRelationTensorHom.equiv (k := ℂ) (localOrdered a b p s) (multiplicityOrdered c d p s)
        (exchangeRelations c d p s) (exchange_stable c d p s)))

def familyEquiv : MixedPatternAssembly.familySpace (fieldF a c) (fieldB b d) p s ≃ₗ[ℂ]
    IntertwiningMap (residual a b c d p s) (trivial ℂ H ℂ) :=
  (MixedPatternAssembly.equiv (fieldF a c) (fieldB b d) p s).trans (equiv a b c d p s)

end
end Math.TypedMixedSeparatedHom
