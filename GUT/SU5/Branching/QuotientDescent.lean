import GUT.SU5.Branching.ExteriorSquare
import GUT.SU5.Embeddings.StandardModelQuotient

open Physics

/-! Descending the actual matter blocks through the proved central kernel.
The quotient representation is constructed on the same SM block spaces,
and its pullback is exactly the original full covering-group action. -/

set_option autoImplicit false

namespace GUT.SU5.QuotientDescent

noncomputable section

open StandardModelEmbedding StandardSMGaugeTensor

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {rho : Representation ℂ TargetGroup V} {sigma : Representation ℂ GaugeGroup W}

theorem kernel_acts_trivially (e : Representation.Equiv (rho.comp hom) sigma)
    (g : GaugeGroup) (hg : g ∈ hom.ker) : sigma g = 1 := by
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := e.surjective w
  have he := e.toIntertwiningMap.isIntertwining _ _ g v
  change e (rho (hom g) v) = sigma g (e v) at he
  rw [show hom g = 1 from hg, map_one, Module.End.one_apply] at he
  exact he.symm

def descend (e : Representation.Equiv (rho.comp hom) sigma) : Representation ℂ SMQuotient W :=
  QuotientGroup.lift hom.ker sigma (fun g hg => kernel_acts_trivially e g hg)

@[simp] theorem descend_mk (e : Representation.Equiv (rho.comp hom) sigma) (g : GaugeGroup) :
    descend e (QuotientGroup.mk g) = sigma g := rfl

def descendEquiv (e : Representation.Equiv (rho.comp hom) sigma) :
    Representation.Equiv (rho.comp quotientHom) (descend e) :=
  .mk e.toLinearEquiv (by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g => exact e.isIntertwining' g)

def five := descend FundamentalBranching.fundamentalEquiv
def barFive := descend FundamentalBranching.antifundamentalEquiv
def ten := descend ExteriorSquareBranching.tenEquiv

def fiveEquiv := descendEquiv FundamentalBranching.fundamentalEquiv
def barFiveEquiv := descendEquiv FundamentalBranching.antifundamentalEquiv
def tenEquiv := descendEquiv ExteriorSquareBranching.tenEquiv

end

end GUT.SU5.QuotientDescent
