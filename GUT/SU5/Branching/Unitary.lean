import GUT.SU5.Representations.UnitaryMatter
import GUT.SU5.Branching.QuotientDescent

open Math

/-! Actual branching and quotient descent of the continuous unitary models.
The algebraic equivalences have already been constructed from vectors, not
postulated as certificates. -/

set_option autoImplicit false

namespace GUT.SU5.UnitaryBranching

noncomputable section

open StandardModelEmbedding SplitRepresentationProjection

def fundamentalEquiv : Representation.Equiv
    (UnitaryMatter.fundamental.toRepresentation.comp hom) FundamentalBranching.blocksRho :=
  (restrictEquiv UnitaryMatter.fundamentalEquiv.symm hom).trans
    FundamentalBranching.fundamentalEquiv

def antifundamentalEquiv : Representation.Equiv
    (UnitaryMatter.antifundamental.toRepresentation.comp hom) FundamentalBranching.barBlocksRho :=
  (restrictEquiv UnitaryMatter.antifundamentalEquiv.symm hom).trans
    FundamentalBranching.antifundamentalEquiv

def tenEquiv : Representation.Equiv
    (UnitaryMatter.ten.toRepresentation.comp hom) ExteriorSquareBranching.blocksRho :=
  (restrictEquiv UnitaryMatter.tenEquiv.symm hom).trans ExteriorSquareBranching.tenEquiv

def quotientFive : ContRepresentation ℂ SMQuotient UnitaryMatter.FiveHilbert :=
  UnitaryMatter.fundamental.restrict quotientHom
def quotientBarFive : ContRepresentation ℂ SMQuotient UnitaryMatter.BarFiveHilbert :=
  UnitaryMatter.antifundamental.restrict quotientHom
def quotientTen : ContRepresentation ℂ SMQuotient UnitaryMatter.TenHilbert :=
  UnitaryMatter.ten.restrict quotientHom

theorem quotientFive_continuous : Continuous quotientFive :=
  UnitaryMatter.fundamental_continuous.comp quotientHom_isEmbedding.continuous
theorem quotientBarFive_continuous : Continuous quotientBarFive :=
  UnitaryMatter.antifundamental_continuous.comp quotientHom_isEmbedding.continuous
theorem quotientTen_continuous : Continuous quotientTen :=
  UnitaryMatter.ten_continuous.comp quotientHom_isEmbedding.continuous

theorem quotientFive_unitary : ContRepresentation.IsUnitary quotientFive :=
  UnitaryMatter.fundamental_unitary.restrict quotientHom
theorem quotientBarFive_unitary : ContRepresentation.IsUnitary quotientBarFive :=
  UnitaryMatter.antifundamental_unitary.restrict quotientHom
theorem quotientTen_unitary : ContRepresentation.IsUnitary quotientTen :=
  UnitaryMatter.ten_unitary.restrict quotientHom

def quotientFiveEquiv : Representation.Equiv quotientFive.toRepresentation QuotientDescent.five :=
  (restrictEquiv UnitaryMatter.fundamentalEquiv.symm quotientHom).trans QuotientDescent.fiveEquiv
def quotientBarFiveEquiv : Representation.Equiv quotientBarFive.toRepresentation QuotientDescent.barFive :=
  (restrictEquiv UnitaryMatter.antifundamentalEquiv.symm quotientHom).trans QuotientDescent.barFiveEquiv
def quotientTenEquiv : Representation.Equiv quotientTen.toRepresentation QuotientDescent.ten :=
  (restrictEquiv UnitaryMatter.tenEquiv.symm quotientHom).trans QuotientDescent.tenEquiv

end

end GUT.SU5.UnitaryBranching
