import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Basic.Complex.Basic

/-!
# Mathlib-backed representation-theoretic inputs

This module records the standard finite-dimensional representation fact used by
the flipped-branch obstruction: characters are traces, and trace characters are
constant on conjugacy classes.
-/

namespace Math
namespace MathlibBridge

open Representation

theorem representation_character_conj
    {G k V : Type*}
    [Group G] [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (ρ : Representation k G V) (g h : G) :
    ρ.character (h * g * h⁻¹) = ρ.character g := by
  simp [ρ.char_conj g h]

abbrev SU6 :=
  Matrix.specialUnitaryGroup (Fin 6) ℂ

theorem su6_representation_character_conj
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ SU6 V) (g h : SU6) :
    ρ.character (h * g * h⁻¹) = ρ.character g := by
  exact representation_character_conj ρ g h

end MathlibBridge
end Math
