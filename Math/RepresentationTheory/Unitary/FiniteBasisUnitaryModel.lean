import Math.LinearAlgebra.Constructions.FiniteBasisHilbertization
import TauCeti.RepresentationTheory.Compact.UnitaryModel

/-!
# Unitary models from continuous finite-basis coordinates

An algebraic representation with continuous matrix coefficients on a compact
group is realized on a finite Hilbert copy. TauCeti's unitarization theorem
supplies an equivalent unitary action. No invariant form or equivalence is
assumed as input, and no ambient Math group is involved.
-/

set_option autoImplicit false

namespace Math.FiniteBasisUnitaryModel

noncomputable section

open FiniteBasisHilbertization

variable {G V ι : Type*} [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module ℂ V] [Fintype ι]
variable (b : Module.Basis ι ℂ V) (rho : Representation ℂ G V)

def copyRho : Representation ℂ G (Copy b) where
  toFun g := (Copy.valLinearEquiv b).symm.toLinearMap.comp
    ((rho g).comp (Copy.valLinearEquiv b).toLinearMap)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [map_mul]

def seed : ContRepresentation ℂ G (Copy b) := .ofMonoidHom {
  toFun g := (copyRho b rho g).toContinuousLinearMap
  map_one' := by ext x; exact LinearMap.congr_fun (map_one (copyRho b rho)) x
  map_mul' g h := by ext x; exact LinearMap.congr_fun (map_mul (copyRho b rho) g h) x }

def seedEquiv : Representation.Equiv rho (seed b rho).toRepresentation :=
  .mk (Copy.valLinearEquiv b).symm (by intro g; ext x; rfl)

theorem seed_continuous
    (h : ∀ i j, Continuous fun g => b.coord i (rho g (b j))) :
    Continuous (seed b rho) := by
  apply continuous_clm_apply.mpr
  intro x
  rw [Copy.continuous_iff_coords]
  intro i
  change Continuous (fun g => b.coord i (rho g x.val))
  have hf : (fun g => b.coord i (rho g x.val)) =
      fun g => ∑ j, (b.repr x.val j) * b.coord i (rho g (b j)) := by
    funext g
    conv_lhs => rw [← b.sum_repr x.val]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hf]
  exact continuous_finsetSum _ (fun j _ => continuous_const.mul (h i j))

variable [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (h : ∀ i j, Continuous fun g => b.coord i (rho g (b j)))

def conjugator : Copy b ≃L[ℂ] Copy b :=
  (ContRepresentation.exists_isUnitary_congr (seed b rho)
    (seed_continuous b rho h)).choose

def model : ContRepresentation ℂ G (Copy b) :=
  ContinuousLinearEquiv.congr (conjugator b rho h) (seed b rho)

theorem model_continuous : Continuous (model b rho h) :=
  ContinuousLinearEquiv.continuous_congr _ (seed_continuous b rho h)

theorem model_unitary : ContRepresentation.IsUnitary (model b rho h) :=
  (ContRepresentation.exists_isUnitary_congr (seed b rho)
    (seed_continuous b rho h)).choose_spec

theorem model_inner (g : G) (x y : Copy b) :
    inner ℂ (model b rho h g x) (model b rho h g y) = inner ℂ x y :=
  (model_unitary b rho h).inner_map_map g x y

theorem model_jointlyContinuous :
    Continuous (fun p : G × Copy b => model b rho h p.1 p.2) := by
  exact ((model_continuous b rho h).comp continuous_fst).clm_apply continuous_snd

def modelEquiv : Representation.Equiv rho (model b rho h).toRepresentation :=
  (seedEquiv b rho).trans (.mk (conjugator b rho h).toLinearEquiv (by
    intro g
    ext x
    change conjugator b rho h (seed b rho g x) =
      conjugator b rho h (seed b rho g ((conjugator b rho h).symm (conjugator b rho h x)))
    rw [ContinuousLinearEquiv.symm_apply_apply]))

end

end Math.FiniteBasisUnitaryModel
