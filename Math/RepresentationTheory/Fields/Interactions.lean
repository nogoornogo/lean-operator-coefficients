import Math.RepresentationTheory.Fields.Selection
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport
import TauCeti.RepresentationTheory.ExteriorPower
import TauCeti.RepresentationTheory.SymmetricPower

/-! Natural interaction restriction, fixed-vacuum insertion and all mixed-degree
statistics-preserving coefficient transport on actual representations. -/
namespace Math.FieldSelection
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G U V W : Type*} [Group G]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {rho : Representation ℂ G U} {sigma : Representation ℂ G V}
  {tau : Representation ℂ G W}

/-- Contragredient pairing requires the actual intertwiner, not a charge label. -/
theorem dual_pairing (t : IntertwiningMap rho sigma)
    (g : G) (f : Module.Dual ℂ V) (u : U) :
    sigma.dual g f (t (rho g u)) = f (t u) := by
  change f (sigma g⁻¹ (t (rho g u))) = _
  rw [IntertwiningMap.isIntertwining, Representation.inv_self_apply]

/-- The fixed-vector condition is local to vacuum insertion. -/
def atVacuum (t : IntertwiningMap (rho.tprod sigma) tau)
    (v : U) (hv : ∀ g, rho g v = v) : IntertwiningMap sigma tau where
  toLinearMap := t.toLinearMap.comp (TensorProduct.mk ℂ U V v)
  isIntertwining' g := by
    apply LinearMap.ext
    intro w
    change t (v ⊗ₜ[ℂ] sigma g w) = tau g (t (v ⊗ₜ[ℂ] w))
    simpa only [Representation.tprod_apply, TensorProduct.map_tmul, hv g] using
      t.isIntertwining _ _ g (v ⊗ₜ[ℂ] w)

@[simp] theorem atVacuum_apply (t : IntertwiningMap (rho.tprod sigma) tau)
    (v : U) (hv : ∀ g, rho g v = v) (w : V) :
    atVacuum t v hv w = t (v ⊗ₜ[ℂ] w) := rfl

section Multilinear
variable {J : Type*} {A B : J → Type*}
  [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)]
  (a : ∀ j, Representation ℂ G (A j)) (b : ∀ j, Representation ℂ G (B j))
  (e : ∀ j, IntertwiningMap (a j) (b j))

/-- One structural statement covers every finite arity and independently typed
species. Exterior/symmetric descent is handled by the mixed-power factory. -/
theorem multilinear_restrict (t : MultilinearMap ℂ B ℂ)
    (ht : ∀ g v, t (fun j => b j g (v j)) = t v) (g : G) (u : ∀ j, A j) :
    (t.compLinearMap (fun j => (e j).toLinearMap)) (fun j => a j g (u j)) =
      (t.compLinearMap (fun j => (e j).toLinearMap)) u := by
  change t (fun j => e j (a j g (u j))) = t (fun j => e j (u j))
  simp_rw [IntertwiningMap.isIntertwining]
  exact ht g _
end Multilinear

section Mixed
variable {U' V' : Type*} [AddCommGroup U'] [Module ℂ U']
  [AddCommGroup V'] [Module ℂ V']
  {rho' : Representation ℂ G U'} {sigma' : Representation ℂ G V'}

def mixedEquiv (e : Equiv rho rho') (f : Equiv sigma sigma') (n m : ℕ) :
    Equiv ((rho.exteriorPower n).tprod (sigma.symmetricPower m))
      ((rho'.exteriorPower n).tprod (sigma'.symmetricPower m)) :=
  ExternalInvariantTensor.tensorEquiv (e.exteriorPower n) (f.symmetricPower m)

def mixedCoefficients (e : Equiv rho rho') (f : Equiv sigma sigma') (n m : ℕ) :=
  InvariantCoefficientTransport.alongEquiv (mixedEquiv e f n m)

theorem mixed_evaluation (e : Equiv rho rho') (f : Equiv sigma sigma') (n m : ℕ)
    (q : InvariantCoefficientTransport.Invariants
      ((rho.exteriorPower n).tprod (sigma.symmetricPower m)))
    (u : ⋀[ℂ]^n U) (v : Sym[ℂ]^m V) :
    mixedCoefficients e f n m q
      (e.exteriorPower n u ⊗ₜ[ℂ] f.symmetricPower m v) = q (u ⊗ₜ[ℂ] v) := by
  change q ((mixedEquiv e f n m).symm
    (mixedEquiv e f n m (u ⊗ₜ[ℂ] v))) = _
  exact congrArg q ((mixedEquiv e f n m).toLinearEquiv.symm_apply_apply _)

theorem mixed_roundtrip (e : Equiv rho rho') (f : Equiv sigma sigma') (n m : ℕ)
    (q : InvariantCoefficientTransport.Invariants
      ((rho.exteriorPower n).tprod (sigma.symmetricPower m))) :
    (mixedCoefficients e f n m).symm (mixedCoefficients e f n m q) = q :=
  (mixedCoefficients e f n m).symm_apply_apply q
end Mixed

section Commuting
variable {H : Type*} [Group H] (a : Representation ℂ G U) (b : Representation ℂ H U)

theorem exterior_commute (h : ∀ g z u, a g (b z u) = b z (a g u))
    (n : ℕ) (g : G) (z : H) (u : ⋀[ℂ]^n U) :
    a.exteriorPower n g (b.exteriorPower n z u) =
      b.exteriorPower n z (a.exteriorPower n g u) := by
  have hc : (a g).comp (b z) = (b z).comp (a g) := LinearMap.ext (h g z)
  change (exteriorPower.map n (a g)).comp (exteriorPower.map n (b z)) u =
    (exteriorPower.map n (b z)).comp (exteriorPower.map n (a g)) u
  rw [← exteriorPower.map_comp, ← exteriorPower.map_comp, hc]
end Commuting
end
end Math.FieldSelection
