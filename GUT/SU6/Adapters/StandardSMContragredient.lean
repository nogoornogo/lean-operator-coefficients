import GUT.SU6.Branching.StandardSMGroup
import Physics.StandardModel.Gauge.WeakContragredient

open Math

/-!
# The weak contragredient in the actual standard branching

The SU(2) epsilon pairing identifies the charge -3 lepton with the dual
of the charge +3 weak block. This is an actual intertwining equivalence,
not an inference from torus characters.
-/

set_option autoImplicit false

namespace GUT.StandardSMContragredient

noncomputable section

open StandardSMGaugeTensor SMEpsilonTensor

abbrev SingletDual := Module.Dual ℂ ℂ

def singletDual : Representation ℂ GaugeGroup SingletDual :=
  (Representation.trivial ℂ GaugeGroup ℂ).dual

def antifundamentalSM : Representation ℂ GaugeGroup
    (Module.Dual ℂ Color × (Weak × SingletDual)) :=
  downRight.dual.prod (lepton.prod singletDual)

def heavyDualEquiv : Representation.Equiv StandardSMGroup.heavy.dual antifundamentalSM :=
  (SplitRepresentationProjection.dualProdEquiv downRight
    ((twist weak 3).prod (Representation.trivial ℂ GaugeGroup ℂ))).symm.trans
    (SplitRepresentationProjection.prodEquiv (Representation.Equiv.refl _)
      ((SplitRepresentationProjection.dualProdEquiv (twist weak 3)
        (Representation.trivial ℂ GaugeGroup ℂ)).symm.trans
          (SplitRepresentationProjection.prodEquiv leptonDualEquiv.symm
            (Representation.Equiv.refl _))))

def antifundamentalEquiv : Representation.Equiv
    (ConcreteSU6Representations.antifundamental.rho.comp StandardSMGroup.hom)
    antifundamentalSM :=
  StandardSMGroup.analyticAntifundamentalEquiv.trans heavyDualEquiv

theorem singletDual_trivial (g : GaugeGroup) (phi : SingletDual) : singletDual g phi = phi := by
  apply LinearMap.ext; intro z
  rfl

end

end GUT.StandardSMContragredient
