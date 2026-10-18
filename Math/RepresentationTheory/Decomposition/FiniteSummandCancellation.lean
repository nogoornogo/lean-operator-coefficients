import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Basic.Complex.Basic
import TauCeti.RingTheory.KrullSchmidt.Cancellation

/-! Cancellation of an actual finite-dimensional common representation.
The group can be infinite. Finite complex dimension implies finite length
over its group algebra; no irreducibility or compactness is assumed. -/
namespace Math.FiniteSummandCancellation
set_option autoImplicit false
noncomputable section
open Representation
open scoped MonoidAlgebra
variable {G A B C : Type*} [Group G]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]
  (r : Representation ℂ G A) (s : Representation ℂ G B) (t : Representation ℂ G C)

def asModuleEquivalence (e : Representation.Equiv r s) : r.asModule ≃ₗ[ℂ[G]] s.asModule :=
  LinearEquiv.ofBijective
    (IntertwiningMap.equivLinearMapAsModule r s e.toIntertwiningMap) e.bijective

def fromModuleEquivalence (e : r.asModule ≃ₗ[ℂ[G]] s.asModule) : Representation.Equiv r s :=
  ((IntertwiningMap.equivLinearMapAsModule r s).symm e.toLinearMap).ofBijective e.bijective

def productModule : (r.prod s).asModule ≃ₗ[ℂ[G]] r.asModule × s.asModule :=
  LinearEquiv.ofBijective
    ((IntertwiningMap.equivLinearMapAsModule (r.prod s) r (IntertwiningMap.fst ℂ r s)).prod
      (IntertwiningMap.equivLinearMapAsModule (r.prod s) s (IntertwiningMap.snd ℂ r s)))
    ⟨fun _x _y h => h,fun x => ⟨x,rfl⟩⟩

theorem finiteLength [FiniteDimensional ℂ C] : IsFiniteLength ℂ[G] t.asModule := by
  have hn : IsNoetherian ℂ[G] t.asModule := isNoetherian_of_tower ℂ (inferInstance : IsNoetherian ℂ t.asModule)
  have ha : IsArtinian ℂ[G] t.asModule := isArtinian_of_tower ℂ (inferInstance : IsArtinian ℂ t.asModule)
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨hn,ha⟩

/-- An actual finite-dimensional common summand cancels, even for an
infinite group and without any simple-module or matching premise. -/
theorem nonempty_equiv [FiniteDimensional ℂ C]
    (e : Representation.Equiv (r.prod t) (s.prod t)) : Nonempty (Representation.Equiv r s) := by
  let em : (r.asModule × t.asModule) ≃ₗ[ℂ[G]] (s.asModule × t.asModule) :=
    (productModule r t).symm.trans ((asModuleEquivalence (r.prod t) (s.prod t) e).trans
      (productModule s t))
  obtain ⟨f⟩ := TauCeti.nonempty_linearEquiv_of_prod_linearEquiv_of_isFiniteLength
    (finiteLength t) ⟨em⟩
  exact ⟨fromModuleEquivalence r s f⟩

end
end Math.FiniteSummandCancellation
