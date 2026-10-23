import Math.RepresentationTheory.Weights.TorusWeightTensor
import Math.RepresentationTheory.SU2.WeakDoubletScalars

/-! Extract an actual SU2 torus weight while retaining every independent
group action. Existence is the uniform interval/parity condition, not a
computed weight multiplicity or an unevaluated representation matching. -/
namespace Math.SU2WeightSlice
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor TorusWeightSlice WeakDoubletScalars
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {K U : Type*} [Group K] [AddCommGroup U] [Module ℂ U]
  (s : Representation ℂ K U)
@[reducible] local instance (m : ℕ) : AddCommGroup (Sym[ℂ]^m Doublet) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance (m : ℕ) : AddCommGroup ((Sym[ℂ]^m Doublet) ⊗[ℂ] U) := inferInstance

def InString (m : ℕ) (n : ℤ) : Prop := -(m : ℤ)≤n ∧ n≤m ∧ (n+m)%2=0

theorem index_iff (m : ℕ) (n : ℤ) :
    (∃ i : Fin (m+1), TauCeti.SU2.weight m i=n) ↔ InString m n := by
  constructor
  · rintro ⟨i, hi⟩
    have hb := i.isLt
    rw [TauCeti.SU2.weight_def] at hi
    dsimp [InString]
    omega
  · rintro ⟨hlo,hhi,hpar⟩
    have hc : (((n+(m : ℤ)).toNat : ℕ) : ℤ)=n+m := by omega
    refine ⟨⟨(n+(m : ℤ)).toNat/2, by omega⟩, ?_⟩
    change (2 : ℤ)*(((n+(m : ℤ)).toNat/2 : ℕ) : ℤ)-(m : ℤ)=n
    omega

abbrev source (m : ℕ) := external (doublet.symmetricPower m) s
abbrev slice (m : ℕ) (n : ℤ) := action (source s m) TauCeti.SU2.torusHom n

theorem basis_eigen (m : ℕ) (z : Circle) (i : Fin (m+1)) :
    (doublet.symmetricPower m) (TauCeti.SU2.torusHom z) (TauCeti.SU2.weightBasis m i)=
      (z : ℂ)^(TauCeti.SU2.weight m i) • TauCeti.SU2.weightBasis m i := by
  rw [symmetricPower_eq]
  exact TauCeti.SU2.symPower_torusHom_weightBasis m z i

def indexed (m : ℕ) (i : Fin (m+1)) : Representation.Equiv s (slice s m (TauCeti.SU2.weight m i)) :=
  TorusWeightTensor.equivalence (doublet.symmetricPower m) s TauCeti.SU2.torusHom
    (TauCeti.SU2.weightBasis m) (TauCeti.SU2.weight m) (basis_eigen m)
      (TauCeti.SU2.weight_injective m) i

/-- Every weight in the SU2 string gives the entire retained representation,
with an actual equivariant equivalence. -/
def equivalence (m : ℕ) (n : ℤ) (hn : InString m n) : Representation.Equiv s (slice s m n) := by
  let i := Classical.choose ((index_iff m n).mpr hn)
  have hi : TauCeti.SU2.weight m i=n := Classical.choose_spec ((index_iff m n).mpr hn)
  exact (indexed s m i).trans
    (TorusWeightSlice.castWeight (source s m) TauCeti.SU2.torusHom hi)

theorem absent_zero (m : ℕ) (n : ℤ) (hn : ¬InString m n)
    (x : Space (source s m) TauCeti.SU2.torusHom n) : x=0 :=
  TorusWeightTensor.absent_zero (doublet.symmetricPower m) s TauCeti.SU2.torusHom
    (TauCeti.SU2.weightBasis m) (TauCeti.SU2.weight m) (basis_eigen m) n
      (fun i hi => hn ((index_iff m n).mp ⟨i,hi⟩)) x

end
end Math.SU2WeightSlice
