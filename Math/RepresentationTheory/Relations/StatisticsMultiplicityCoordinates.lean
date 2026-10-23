import Math.RepresentationTheory.Relations.CommutingStatisticsModule
import Math.RepresentationTheory.Constructions.MultiplicityCoordinates
import Mathlib.Algebra.Group.Finsupp

/-! Simple-copy coordinates for the actual statistics blocks, including the
full residual action and inverse coefficient reconstruction. -/
namespace Math.StatisticsMultiplicityCoordinates
set_option autoImplicit false
noncomputable section
open Representation
open scoped MonoidAlgebra
universe u

structure Presentation (R : Type*) (M : Type u) [Ring R]
    [AddCommGroup M] [Module R M] where
  Index : Type u
  simple : Submodule R M
  isSimple : IsSimpleModule R simple
  coordinates : M ≃ₗ[R] Index →₀ simple

variable {k H S : Type*} {U : Type u} [Field k] [Group H] [Group S]
  [AddCommGroup U] [Module k U] [Finite S] [NeZero (Nat.card S : k)]
  (rho : Representation k H U) (b : Representation k S U)
  (commutes : ∀ g h u, b g (rho h u) = rho h (b g u))

/-- Existence is proved; the choice of simple copies is deliberately noncanonical. -/
def chosen (c : CommutingStatisticsModule.Index b) : Presentation k[S] c.1 :=
  Classical.choice (show Nonempty (Presentation k[S] c.1) from by
    obtain ⟨I, _, V, hs, e⟩ := MultiplicityCoordinates.exists_block_coordinates c
    exact ⟨⟨I, V, hs, e.some⟩⟩)

variable (P : ∀ c : CommutingStatisticsModule.Index b, Presentation k[S] c.1)

abbrev Carrier (c : CommutingStatisticsModule.Index b) := (P c).Index →₀ (P c).simple

def coordinates (c : CommutingStatisticsModule.Index b) : c.1 ≃ₗ[k] Carrier b P c :=
  (P c).coordinates.restrictScalars k

instance (c : CommutingStatisticsModule.Index b) : AddCommGroup (Carrier b P c) := by
  letI : AddCommGroup ((P c).simple) := inferInstance
  exact Finsupp.instAddCommGroup

def residual (c : CommutingStatisticsModule.Index b) : Representation k H (Carrier b P c) :=
  MultiplicityCoordinates.action (N := Carrier b P c)
    (CommutingStatisticsModule.block rho b commutes c)
    (coordinates b P c)

variable {W : Type*} [AddCommGroup W] [Module k W] (w : Representation k H W)

/-- The block-Hom product is refined to actual simple-copy coordinates. -/
def coefficientEquiv : IntertwiningMap rho w ≃ₗ[k]
    (∀ c, IntertwiningMap (residual rho b commutes P c) w) :=
  (CommutingStatisticsModule.coefficientEquiv rho b commutes w).trans
    (LinearEquiv.piCongrRight fun c => MultiplicityCoordinates.coefficientEquiv
      (CommutingStatisticsModule.block rho b commutes c) (coordinates b P c) w)

@[simp] theorem extraction (f : IntertwiningMap rho w)
    (c : CommutingStatisticsModule.Index b) (z : Carrier b P c) :
    coefficientEquiv rho b commutes P w f c z =
      f (b.asModuleEquiv ((coordinates b P c).symm z)) := by
  exact CommutingStatisticsModule.coefficientEquiv_apply rho b commutes w f c _

@[simp] theorem reconstruction
    (q : ∀ c, IntertwiningMap (residual rho b commutes P c) w)
    (c : CommutingStatisticsModule.Index b) (z : c.1) :
    (coefficientEquiv rho b commutes P w).symm q (b.asModuleEquiv z) =
      q c (coordinates b P c z) := by
  have h := congrArg (fun t => t c (coordinates b P c z))
    ((coefficientEquiv rho b commutes P w).apply_symm_apply q)
  simpa only [extraction, LinearEquiv.symm_apply_apply] using h

theorem zero_iff (f : IntertwiningMap rho w) :
    f = 0 ↔ ∀ c, coefficientEquiv rho b commutes P w f c = 0 := by
  rw [← (coefficientEquiv rho b commutes P w).map_eq_zero_iff]
  exact funext_iff

/-- No coordinate existence premise is required of the consumer. -/
def chosenCoefficientEquiv := coefficientEquiv rho b commutes (chosen b) w

variable (Q : ∀ c : CommutingStatisticsModule.Index b, Presentation k[S] c.1)

/-- Different choices describe the same original residual coefficients. -/
def change : (∀ c, IntertwiningMap (residual rho b commutes P c) w) ≃ₗ[k]
    (∀ c, IntertwiningMap (residual rho b commutes Q c) w) :=
  (coefficientEquiv rho b commutes P w).symm.trans
    (coefficientEquiv rho b commutes Q w)

@[simp] theorem change_apply
    (q : ∀ c, IntertwiningMap (residual rho b commutes P c) w)
    (c : CommutingStatisticsModule.Index b) (z : Carrier b Q c) :
    change rho b commutes P w Q q c z =
      q c (coordinates b P c ((coordinates b Q c).symm z)) := by
  rw [change, LinearEquiv.trans_apply, extraction, reconstruction]

theorem change_inverse
    (q : ∀ c, IntertwiningMap (residual rho b commutes P c) w) :
    change rho b commutes Q w P (change rho b commutes P w Q q) = q := by
  simp [change]

end
end Math.StatisticsMultiplicityCoordinates
