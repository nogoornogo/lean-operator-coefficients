import Math.RepresentationTheory.BoundedHiggsSupport

/-! An actual Clebsch--Gordan embedding of charged weak constituents.
Scalar characters add exactly, without discarding hypercharge phases. -/
namespace Math.TwistedSU2ConstituentCoupling
set_option autoImplicit false
noncomputable section
open Representation WeakDoubletScalars
open scoped TensorProduct
variable {G : Type*} [Group G] (j : G →* TauCeti.SU2) (chi : G →* ℂˣ)

@[reducible] local instance (x y : ℕ) : AddCommGroup (Sym[ℂ]^x Doublet ⊗[ℂ] Sym[ℂ]^y Doublet) := inferInstance

def embed (x y : ℕ) (r : SU2ClebschGordan.Index x y) (delta epsilon : ℤ) :
    IntertwiningMap (BoundedHiggsSupport.constituent j chi (SU2ClebschGordan.degree x y r) (delta+epsilon))
      ((BoundedHiggsSupport.constituent j chi x delta).tprod
        (BoundedHiggsSupport.constituent j chi y epsilon)) where
  toLinearMap := (SU2ClebschGordan.embed x y r).toLinearMap
  isIntertwining' g := by
    have ht := (CharacterTwistTransport.tensor (chi^delta) (chi^epsilon)
      ((doublet.symmetricPower x).comp j) ((doublet.symmetricPower y).comp j)).isIntertwining' g
    change ((BoundedHiggsSupport.constituent j chi x delta).tprod
      (BoundedHiggsSupport.constituent j chi y epsilon)) g =
        charTwist (chi^delta*chi^epsilon)
          (Representation.tprod ((doublet.symmetricPower x).comp j) ((doublet.symmetricPower y).comp j)) g at ht
    apply LinearMap.ext
    intro v
    change SU2ClebschGordan.embed x y r
      ((((chi^(delta+epsilon)) g : ℂˣ) : ℂ) • doublet.symmetricPower _ (j g) v)=_
    rw [ht]
    change SU2ClebschGordan.embed x y r
      ((((chi^(delta+epsilon)) g : ℂˣ) : ℂ) • doublet.symmetricPower _ (j g) v)=
        (((chi^delta*chi^epsilon) g : ℂˣ) : ℂ) • SU2ClebschGordan.Tensor x y (j g)
          (SU2ClebschGordan.embed x y r v)
    rw [map_smul,zpow_add chi delta epsilon]
    exact congrArg (fun z => (((chi^delta*chi^epsilon) g : ℂˣ) : ℂ) • z)
      ((SU2ClebschGordan.embed x y r).isIntertwining _ _ (j g) v)

theorem embed_injective (x y : ℕ) (r : SU2ClebschGordan.Index x y) (delta epsilon : ℤ) :
    Function.Injective (embed j chi x y r delta epsilon) := SU2ClebschGordan.embed_injective x y r

end
end Math.TwistedSU2ConstituentCoupling
