import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RepresentationTheory.Intertwining

/-! Nonredundant isotypic decomposition compatible with a residual action.
The residual action is linear over the statistics algebra. No dimension or
finiteness assumption on the module or its multiplicities is used. -/
namespace Math.IsotypicResidual
set_option autoImplicit false
noncomputable section
open Representation
variable {R H M : Type*} [Ring R] [Group H] [AddCommGroup M] [Module R M]
  [IsSemisimpleModule R M] (rho : Representation R H M)

abbrev Index := isotypicComponents R M

omit [IsSemisimpleModule R M] in
theorem stable (c : Index (R := R) (M := M)) (h : H) :
    c.1 ≤ c.1.comap (rho h) :=
  Submodule.IsFullyInvariant.of_mem_isotypicComponents c.2 (rho h)

abbrev component (c : Index (R := R) (M := M)) :=
  rho.subrepresentation c.1 (stable rho c)

def sumEquiv : Representation.Equiv
    (Representation.directSum (component rho)) rho where
  toLinearEquiv := by
    classical
    exact ((sSupIndep_iff _).mp (sSupIndep_isotypicComponents R M)).linearEquiv
      ((sSup_eq_iSup' _).symm.trans (sSup_isotypicComponents R M))
  isIntertwining' h := by
    classical
    apply DirectSum.linearMap_ext
    intro c
    apply LinearMap.ext
    intro x
    change DFinsupp.lsum ℕ (fun c : Index (R := R) (M := M) => c.1.subtype)
      ((DirectSum.lmap (fun c => component rho c h))
        (DirectSum.of (fun c : Index (R := R) (M := M) => c.1) c x)) =
      rho h (DFinsupp.lsum ℕ (fun c : Index (R := R) (M := M) => c.1.subtype)
        (DFinsupp.single c x))
    rw [DirectSum.lmap_of]
    change DFinsupp.lsum ℕ (fun c : Index (R := R) (M := M) => c.1.subtype)
      (DFinsupp.single c ((component rho c h) x)) =
      rho h (DFinsupp.lsum ℕ (fun c : Index (R := R) (M := M) => c.1.subtype)
        (DFinsupp.single c x))
    simp

@[simp] theorem sumEquiv_single (c : Index (R := R) (M := M)) (x : c.1) :
    sumEquiv rho (DFinsupp.single c x) = x := by
  classical
  change DFinsupp.lsum ℕ (fun c : Index (R := R) (M := M) => c.1.subtype)
    (DFinsupp.single c x) = x
  simp

@[simp] theorem sumEquiv_symm_component (c : Index (R := R) (M := M)) (x : c.1) :
    (sumEquiv rho).symm (x : M) = DFinsupp.single c x := by
  apply (sumEquiv rho).toLinearEquiv.injective
  simp

end
end Math.IsotypicResidual
