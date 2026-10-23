import Math.RepresentationTheory.Decomposition.AlgebraicCommonKernel
import Math.RepresentationTheory.Decomposition.SemisimpleSplitting
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueSpinorExterior
import Math.RepresentationTheory.Characters.CharacterExact

/-! Common actual kernel splits for arbitrary groups and semisimple source.
No topology, target semisimplicity or invariant metric enters this theorem. -/
namespace Physics.AlgebraicCommonCopyKernel
set_option autoImplicit false
noncomputable section
open Math Representation SplitRepresentationProjection
open scoped MonoidAlgebra
variable {H S T : Type*} [Group H]
  [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
  [AddCommGroup T] [Module ℂ T] [FiniteDimensional ℂ T]
  (s : Representation ℂ H S) (t : Representation ℂ H T)

abbrev Components := AlgebraicCommonKernel.Components (R := ℂ[H]) (M := s.asModule)
abbrev Carrier (c : Components s) := AlgebraicCommonKernel.simple c

def action (c : Components s) : Representation ℂ H (Carrier s c) :=
  Representation.ofModule' (Carrier s c)

section Kernel
variable (M : IntertwiningMap s t)

def simpleToKernel (P : Submodule ℂ[H] s.asModule)
    (hp : P ≤ (IntertwiningMap.equivLinearMapAsModule s t M).ker) :
    IntertwiningMap (Representation.ofModule' P) M.ker.toRepresentation where
  toLinearMap := {
    toFun := fun x => ⟨x.val, hp x.property⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro z x; rfl }
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (MonoidAlgebra.single h (1 : ℂ)) • (x.val : s.asModule) = s h x.val
    rw [Representation.single_smul, one_smul]
    rfl

omit [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] in
theorem kernel_semisimple (hs : IsSemisimpleRepresentation s) :
    IsSemisimpleRepresentation M.ker.toRepresentation := by
  let : IsSemisimpleModule ℂ[H] s.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule s).mp hs
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  exact IsSemisimpleModule.of_injective
    (IntertwiningMap.equivLinearMapAsModule M.ker.toRepresentation s
      (CharacterExact.subtypeIntertwiner M.ker)) Subtype.val_injective

end Kernel

section ModuleEquiv
variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [Module ℂ[H] A]
  [IsScalarTower ℂ ℂ[H] A] [AddCommGroup B] [Module ℂ B] [Module ℂ[H] B]
  [IsScalarTower ℂ ℂ[H] B]

def ofModuleEquiv (e : A ≃ₗ[ℂ[H]] B) :
    Representation.Equiv (Representation.ofModule' (k := ℂ) (G := H) A) (Representation.ofModule' (k := ℂ) (G := H) B) where
  toLinearEquiv := e.restrictScalars ℂ
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    exact e.map_smul (MonoidAlgebra.single h 1) x

end ModuleEquiv

omit [FiniteDimensional ℂ S] in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
/-- One actual split simple constituent survives all three maps. Source
semisimplicity replaces compactness/continuity; target semisimplicity is absent. -/
theorem exists_common_split (hs : IsSemisimpleRepresentation s)
    (Mq Mu Me : IntertwiningMap s t) (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    ∃ c : Components s, Nontrivial (Carrier s c) ∧
      Nonempty (Split Mq.ker.toRepresentation (action s c)) ∧
      Nonempty (Split Mu.ker.toRepresentation (action s c)) ∧
      Nonempty (Split Me.ker.toRepresentation (action s c)) := by
  let : IsSemisimpleModule ℂ[H] s.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule s).mp hs
  let maps : Fin 3 → IntertwiningMap s t := ![Mq,Mu,Me]
  obtain ⟨c,hc⟩ := AlgebraicCommonKernel.exists_common_simple_kernel (k := ℂ)
    (M := s.asModule) (N := t.asModule)
    (fun j => IntertwiningMap.equivLinearMapAsModule s t (maps j)) hd
  have split (j : Fin 3) : Nonempty (Split (maps j).ker.toRepresentation (action s c)) := by
    obtain ⟨P,hp,hP,⟨e⟩⟩ := hc j
    let i := simpleToKernel s t (maps j) P hp
    have hi : Function.Injective i := by
      intro x y he
      have hv : x.val = y.val := congrArg
        (fun z : (maps j).ker.toSubmodule => z.val) he
      exact Subtype.ext hv
    obtain ⟨sp,_⟩ := SemisimpleSplitting.exists_retraction _ _
      (kernel_semisimple s t (maps j) hs) i hi
    exact ⟨sp.trans (Split.ofEquiv (ofModuleEquiv e))⟩
  let : IsSimpleModule ℂ[H] (Carrier s c) := AlgebraicCommonKernel.simpleInstance c
  exact ⟨c,IsSimpleModule.nontrivial ℂ[H] (Carrier s c),split 0,split 1,split 2⟩


omit [FiniteDimensional ℂ S] in
theorem kernel_physical_exterior (hs : IsSemisimpleRepresentation s)
    (Mq Mu Me : IntertwiningMap s t) (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    QqueSpinorExterior.HasModelExterior (a := Mq.ker.toRepresentation)
      (b := Mu.ker.toRepresentation) (d := Me.ker.toRepresentation) := by
  obtain ⟨c,hn,⟨sq⟩,⟨su⟩,⟨se⟩⟩ := exists_common_split s t hs Mq Mu Me hd
  let : Nontrivial (Carrier s c) := hn
  exact QqueSpinorExterior.hasModelExterior sq su se

end
end Physics.AlgebraicCommonCopyKernel
