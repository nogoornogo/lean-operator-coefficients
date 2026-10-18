import Math.RepresentationTheory.Decomposition.FiniteConstituentSupport
import Math.RepresentationTheory.Decomposition.CompactIrreducibleQuotient
import Math.RepresentationTheory.Characters.CompactHomDimension
import Math.RepresentationTheory.BoundedTorusWeights
import TauCeti.RepresentationTheory.SU2.Exhaustion

/-! Complete finite SU2 branching with labels bounded by the actual torus
support. Repeated labels retain their distinct copies. There is no evaluated
character, multiplicity, matrix or exterior basis. -/
namespace Math.SU2FiniteBranching
set_option autoImplicit false
noncomputable section
open Representation FiniteSemisimpleDecomposition ContinuousRepresentationScope
open BoundedTorusWeights WeakDoubletScalars

theorem symmetricPower_bound (m N : ℕ)
    (h : Bounded (doublet.symmetricPower m) TauCeti.SU2.torusHom N) : m ≤ N := by
  by_contra hn
  have he : ∀ i, Eigen (doublet.symmetricPower m) TauCeti.SU2.torusHom
      (TauCeti.SU2.weight m i) (TauCeti.SU2.weightBasis m i) := by
    intro i z
    rw [symmetricPower_eq]
    exact TauCeti.SU2.symPower_torusHom_weightBasis m z i
  have hd := dual_basis_eigen (doublet.symmetricPower m) TauCeti.SU2.torusHom
    (TauCeti.SU2.weightBasis m) (TauCeti.SU2.weight m) he (Fin.last m)
  rw [TauCeti.SU2.weight_last] at hd
  have hz := dual_eigen_zero (doublet.symmetricPower m) TauCeti.SU2.torusHom N h
    (-(m : ℤ)) (Or.inr (by omega)) _ hd
  exact (TauCeti.SU2.weightBasis m).dualBasis.ne_zero (Fin.last m) hz

section Algebraic
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ TauCeti.SU2 V) (N : ℕ)

theorem transport_bound {W : Type*} [AddCommGroup W] [Module ℂ W]
    {a : Representation ℂ TauCeti.SU2 V} {b : Representation ℂ TauCeti.SU2 W}
    (e : Representation.Equiv a b) (h : Bounded a TauCeti.SU2.torusHom N) :
    Bounded b TauCeti.SU2.torusHom N :=
  bounded_of_surjective a TauCeti.SU2.torusHom b e.toIntertwiningMap e.surjective N h

/-- Every block of a genuine complete sum has a bounded symmetric-power label. -/
structure Certificate where
  decomposition : Decomposition rho
  degree : Fin decomposition.numberOfBlocks → Fin (N+1)
  blockEquiv : ∀ i, Representation.Equiv
    (doublet.symmetricPower (degree i).val) (decomposition.blockRepresentation i)

namespace Certificate
variable {rho N} (C : Certificate rho N)

abbrev summand (i : Fin C.decomposition.numberOfBlocks) :=
  doublet.symmetricPower (C.degree i).val

/-- Completeness is an equivariant equivalence, not just a list of injections. -/
def equivalence : Representation.Equiv
    (FiniteBlockHom.action C.summand) rho :=
  (show Representation.Equiv (FiniteBlockHom.action C.summand)
      (FiniteBlockHom.action C.decomposition.blockRepresentation) from
    { toLinearEquiv := LinearEquiv.piCongrRight (fun i => (C.blockEquiv i).toLinearEquiv)
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        funext i
        exact (C.blockEquiv i).toIntertwiningMap.isIntertwining _ _ g (x i) }).trans
    (FiniteConstituentSupport.piEquiv C.decomposition).symm

end Certificate
end Algebraic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (rho : Representation ℂ TauCeti.SU2 V) (N : ℕ)

/-- The decomposition and its bounded labels are constructed from continuity
and the already-proved weight bound, without a new branching premise. -/
theorem exists_certificate (hr : IsJointlyContinuous rho)
    (hb : Bounded rho TauCeti.SU2.torusHom N) : Nonempty (Certificate rho N) := by
  classical
  obtain ⟨D⟩ := exists_decomposition rho (CompactIrreducibleQuotient.semisimple rho hr)
  have hblocks (i : Fin D.numberOfBlocks) :
      ∃ m : Fin (N+1), Nonempty (Representation.Equiv
        (doublet.symmetricPower m.val) (D.blockRepresentation i)) := by
    let S := D.subrepresentation i
    have hc := D.subrepresentation_jointlyContinuous i hr
    have hi := D.subrepresentation_isIrreducible i
    obtain ⟨m, ⟨e⟩⟩ := TauCeti.SU2.exists_nonempty_equiv_symPower
      (CompactHomDimension.asContinuous S.toRepresentation)
      (CompactHomDimension.continuous_asContinuous S.toRepresentation hc) hi
    change Representation.Equiv (TauCeti.SU2.symPower m) S.toRepresentation at e
    rw [← symmetricPower_eq] at e
    let t := e.trans (D.blockAmbientEquiv i).symm
    let p := t.symm.toIntertwiningMap.comp (FiniteIrreducibleQuotient.blockProjection D i)
    have hp : Function.Surjective p :=
      t.symm.surjective.comp (FiniteIrreducibleQuotient.blockProjection_surjective D i)
    have hm : m ≤ N := symmetricPower_bound m N
      (bounded_of_surjective rho TauCeti.SU2.torusHom _ p hp N hb)
    exact ⟨⟨m, by omega⟩, ⟨t⟩⟩
  choose m hm using hblocks
  exact ⟨⟨D, m, fun i => Classical.choice (hm i)⟩⟩

/-- A dimension bound suffices when a sharper torus bound is not yet
available. The dimension remains symbolic, including for multiplicity ranges. -/
theorem exists_certificate_of_dimension (hr : IsJointlyContinuous rho) :
    Nonempty (Certificate rho (Module.finrank ℂ V)) := by
  classical
  obtain ⟨D⟩ := exists_decomposition rho (CompactIrreducibleQuotient.semisimple rho hr)
  have hblocks (i : Fin D.numberOfBlocks) :
      ∃ m : Fin (Module.finrank ℂ V+1), Nonempty (Representation.Equiv
        (doublet.symmetricPower m.val) (D.blockRepresentation i)) := by
    let S := D.subrepresentation i
    have hc := D.subrepresentation_jointlyContinuous i hr
    obtain ⟨m, ⟨e⟩⟩ := TauCeti.SU2.exists_nonempty_equiv_symPower
      (CompactHomDimension.asContinuous S.toRepresentation)
      (CompactHomDimension.continuous_asContinuous S.toRepresentation hc)
      (D.subrepresentation_isIrreducible i)
    change Representation.Equiv (TauCeti.SU2.symPower m) S.toRepresentation at e
    rw [← symmetricPower_eq] at e
    let t := e.trans (D.blockAmbientEquiv i).symm
    have hm : m+1 ≤ Module.finrank ℂ V := by
      have hd := D.block_finrank_le i
      rw [← t.finrank_eq, TauCeti.SU2.finrank_symPower] at hd
      exact hd
    exact ⟨⟨m, by omega⟩, ⟨t⟩⟩
  choose m hm using hblocks
  exact ⟨⟨D, m, fun i => Classical.choice (hm i)⟩⟩

end
end Math.SU2FiniteBranching
