import Math.RepresentationTheory.Multiplicity.UnitaryMultiplicity
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.RepresentationTheory.Character

/-! The Hilbert direct sum of two representations, with its original
algebraic product action and trace preserved explicitly. -/

set_option autoImplicit false

namespace Math.HilbertProductRepresentation

noncomputable section

variable {G E F : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (rho : Representation ℂ G E) (sigma : Representation ℂ G F)

def action : Representation ℂ G (WithLp 2 (E × F)) where
  toFun g := (WithLp.linearEquiv 2 ℂ _).symm.conj ((rho.prod sigma) g)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

def equiv : Representation.Equiv (action rho sigma) (rho.prod sigma) :=
  .mk (WithLp.linearEquiv 2 ℂ _) (by
    intro g
    apply LinearMap.ext
    intro x
    simp [action])

theorem unitary (hr : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (hs : UnitaryMultiplicity.IsUnitaryRepresentation sigma) :
    UnitaryMultiplicity.IsUnitaryRepresentation (action rho sigma) := by
  intro g x y
  change inner ℂ (rho g (WithLp.ofLp x).1) (rho g (WithLp.ofLp y).1) +
    inner ℂ (sigma g (WithLp.ofLp x).2) (sigma g (WithLp.ofLp y).2) =
    inner ℂ (WithLp.ofLp x).1 (WithLp.ofLp y).1 + inner ℂ (WithLp.ofLp x).2 (WithLp.ofLp y).2
  rw [hr, hs]

theorem character [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (g : G) :
    (action rho sigma).character g = rho.character g + sigma.character g := by
  rw [congrFun (Representation.char_iso (equiv rho sigma)) g]
  exact LinearMap.trace_prodMap' (rho g) (sigma g)

theorem jointlyContinuous [TopologicalSpace G]
    (hr : Continuous (fun p : G × E => rho p.1 p.2))
    (hs : Continuous (fun p : G × F => sigma p.1 p.2)) :
    Continuous (fun p : G × WithLp 2 (E × F) => action rho sigma p.1 p.2) :=
  (WithLp.prod_continuous_toLp 2 E F).comp
    ((hr.comp (continuous_fst.prodMk
      ((continuous_fst.comp (WithLp.prod_continuous_ofLp 2 E F)).comp continuous_snd))).prodMk
      (hs.comp (continuous_fst.prodMk
        ((continuous_snd.comp (WithLp.prod_continuous_ofLp 2 E F)).comp continuous_snd))))

end

end Math.HilbertProductRepresentation
