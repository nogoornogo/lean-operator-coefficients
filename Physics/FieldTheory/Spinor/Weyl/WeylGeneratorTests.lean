import Physics.FieldTheory.Spinor.Weyl.WeylSpinor
import Math.RepresentationTheory.Invariants.GeneratorInvariantTests
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-! Invariant tests on actual SL(2,C) transvections. Representations may
retain the joint left/entrywise-conjugate-right Weyl action. -/
namespace Physics.WeylGeneratorTests
set_option autoImplicit false
noncomputable section
open Math Representation
abbrev Index := Matrix.TransvectionStruct (Fin 2) ℂ
def generator (t : Index) : WeylSpinor.Group := t.toSpecialLinearGroup

theorem generates : Subgroup.closure (Set.range generator) = ⊤ :=
  Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ WeylSpinor.Group V)

theorem invariant_iff (f : Module.Dual ℂ V) :
    (∀ g x, f (rho g x) = f x) ↔ ∀ t x, f (rho (generator t) x) = f x :=
  GeneratorInvariantTests.invariant_iff rho generator generates f

end
end Physics.WeylGeneratorTests
