import Math.RepresentationTheory.Exterior.ExteriorCubeDoubletCauchy
import Math.RepresentationTheory.Exterior.ExteriorSquareCauchy
import Math.RepresentationTheory.SU2.DoubletCubicHook
import Math.RepresentationTheory.Decomposition.FiniteSummandCancellation
import Math.RepresentationTheory.Decomposition.TensorProductSums

/-! Four actual components of the cubic hook of a space tensor a doublet.
The source is completely expanded by universal Cauchy/hook equivalences;
proved finite-length cancellation removes its known exterior-cube quotient.
No color irreducibility, character identity or branching premise is assumed. -/
namespace Math.ExteriorCubeDoubletHook
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {G A : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  (r : Representation ℂ G A) (j : G →* WeakDoubletScalars.Group)
abbrev B := WeakDoubletScalars.Doublet
abbrev spin := DoubletCubicHook.spin j
abbrev X := r.exteriorPower 3
abbrev H := ExteriorCubeHookRepresentation.action r
abbrev Y := r.symmetricPower 3
abbrev U := r.tprod (spin j)
abbrev source := ExteriorCubeHookRepresentation.source (U r j)
abbrev totalHook := ExteriorCubeHookRepresentation.action (U r j)
abbrev a := (X r).tprod ((spin j).symmetricPower 3)
abbrev b := (X r).tprod (spin j)
abbrev c := (H r).tprod ((spin j).symmetricPower 3)
abbrev d := (H r).tprod (spin j)
abbrev e := (Y r).tprod (spin j)
abbrev common := (a r j).prod (d r j)
abbrev branches := ((b r j).prod (c r j)).prod ((e r j).prod (d r j))
abbrev firstSource := (ExteriorCubeHookRepresentation.source r).tprod
  (SymmetricCubeHookRepresentation.source (spin j))
abbrev secondSource := (SymmetricCubeHookRepresentation.source r).tprod
  (ExteriorCubeHookRepresentation.source (spin j))
abbrev CommonCarrier := ((⋀[ℂ]^3 A) ⊗[ℂ] Sym[ℂ]^3 B) ×
  (ExteriorCubeHook.Hook (V := A) ⊗[ℂ] B)
abbrev BranchCarrier := (((⋀[ℂ]^3 A) ⊗[ℂ] B) ×
  (ExteriorCubeHook.Hook (V := A) ⊗[ℂ] Sym[ℂ]^3 B)) ×
  (((Sym[ℂ]^3 A) ⊗[ℂ] B) × (ExteriorCubeHook.Hook (V := A) ⊗[ℂ] B))

@[reducible] local instance : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Source (V := A)) := inferInstance
@[reducible] local instance : AddCommGroup (SymmetricCubeHook.Source (A := A)) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Source (V := B)) := inferInstance
@[reducible] local instance : AddCommGroup (SymmetricCubeHook.Source (A := B)) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Hook (V := A)) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Hook (V := A ⊗[ℂ] B)) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^3 A) ⊗[ℂ] Sym[ℂ]^3 B) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^3 A) ⊗[ℂ] B) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Hook (V := A) ⊗[ℂ] Sym[ℂ]^3 B) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Hook (V := A) ⊗[ℂ] B) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup ((Sym[ℂ]^3 A) ⊗[ℂ] B) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (CommonCarrier (A := A)) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (BranchCarrier (A := A)) := Module.addCommMonoidToAddCommGroup ℂ

theorem common_finite [FiniteDimensional ℂ A] : Module.Finite ℂ (CommonCarrier (A := A)) := by
  infer_instance

local instance [FiniteDimensional ℂ A] : Module.Finite ℂ (CommonCarrier (A := A)) := common_finite

def sourceCauchy : Representation.Equiv (source r j) ((firstSource r j).prod (secondSource r j)) :=
  (tensorEquiv (.refl (U r j)) (ExteriorSquareCauchyRepresentation.equivalence r (spin j))).trans
    ((TensorProductSums.prodRight (U r j)
      (ExteriorSquareCauchyRepresentation.firstAction r (spin j))
      (ExteriorSquareCauchyRepresentation.secondAction r (spin j))).trans
        (prodEquiv
          (regroupPairDiagonal r (r.exteriorPower 2) (spin j) ((spin j).symmetricPower 2))
          (regroupPairDiagonal r (r.symmetricPower 2) (spin j) ((spin j).exteriorPower 2))))

def firstExpand : Representation.Equiv (firstSource r j)
    (((a r j).prod (b r j)).prod ((c r j).prod (d r j))) :=
  (tensorEquiv (ExteriorCubeHookRepresentation.split r) (DoubletCubicHook.symmetricSource j)).trans
    (TensorProductSums.expand (X r) (H r) ((spin j).symmetricPower 3) (spin j))

def secondExpand : Representation.Equiv (secondSource r j) ((e r j).prod (d r j)) :=
  (tensorEquiv (SymmetricCubeHookRepresentation.equivalence r) (DoubletCubicHook.exteriorSource j)).trans
    (TensorProductSums.prodLeft (Y r) (H r) (spin j))

/-- Six actual summands, regrouped into four candidates and the known cube. -/
def sourceExpanded : Representation.Equiv (source r j) ((branches r j).prod (common r j)) :=
  (sourceCauchy r j).trans ((prodEquiv (firstExpand r j) (secondExpand r j)).trans
    (TensorProductSums.sixReorder (a r j) (b r j) (c r j) (d r j) (e r j) (d r j)))

def sourceHook [FiniteDimensional ℂ A] :
    Representation.Equiv (source r j) ((totalHook r j).prod (common r j)) :=
  (ExteriorCubeHookRepresentation.split (U r j)).trans
    ((prodEquiv (ExteriorCubeDoubletCauchyRepresentation.equivalence r j).symm
      (.refl (totalHook r j))).trans (TensorProductSums.prodComm (common r j) (totalHook r j)))

theorem nonempty_equiv [FiniteDimensional ℂ A] :
    Nonempty (Representation.Equiv (totalHook r j) (branches r j)) :=
  FiniteSummandCancellation.nonempty_equiv
    (A := ExteriorCubeHook.Hook (V := A ⊗[ℂ] B))
    (B := BranchCarrier (A := A)) (C := CommonCarrier (A := A))
    (totalHook r j) (branches r j) (common r j)
    ((sourceHook r j).symm.trans (sourceExpanded r j))

/-- Complete four-branch cubic hook decomposition, obtained from proved
source equivalences and cancellation, not an assumed matching predicate. -/
def equivalence [FiniteDimensional ℂ A] : Representation.Equiv (totalHook r j) (branches r j) :=
  Classical.choice (nonempty_equiv r j)

end
end Math.ExteriorCubeDoubletHook
