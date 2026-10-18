import Math.Audit.ImportOrigin
import Math.LieAlgebras.MatrixLieCertificate
import Lean.Util.CollectAxioms

/-! A small independent sl2 certificate and an import-boundary regression. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`TauCeti).isPrefixOf mod || (`GUT.E6).isPrefixOf mod ||
        (`GUT.SU6).isPrefixOf mod || (`GUT.Spin).isPrefixOf mod then
      throwError "Generic certificate audit imports model data: {mod}"

namespace Math.MatrixLieCertificate.Audit

open SparseMatrixCertificate

attribute [local instance 100] LieRing.ofAssociativeRing

def vectors : Fin 3 → Code (Fin 2) :=
  ![[((0, 1), 1)], [((1, 0), 1)], [((0, 0), 1), ((1, 1), -1)]]

def generators : Fin 2 → Code (Fin 2) := ![vectors 0, vectors 1]
def origin : Fin 3 → Fin 2 ⊕ (Fin 2 × Fin 3) := ![.inl 0, .inl 1, .inr (0, 1)]
def indices : Fin 2 → Fin 3 := ![0, 1]
def coefficients : Fin 2 → Fin 3 → List (Fin 3 × ℤ) :=
  ![![[], [(2, 1)], [(0, -2)]], ![[(2, -1)], [], [(1, 2)]]]
def duals : Fin 3 → Code (Fin 2) := ![[((0, 1), 1)], [((1, 0), 1)], [((0, 0), 1)]]

theorem sl2_finrank : Module.finrank ℚ
    (LieSubalgebra.lieSpan ℚ (Matrix (Fin 2) (Fin 2) ℚ)
      (Set.range fun i => realize ℚ (generators i))).toSubmodule = 3 := by
  apply finrank_generated ℚ vectors duals (fun _ => 1) generators origin indices coefficients
  all_goals decide +kernel

end Math.MatrixLieCertificate.Audit

run_cmd do
  let decl := ``Math.MatrixLieCertificate.Audit.sl2_finrank
  let axioms ← Lean.collectAxioms decl
  for ax in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Generic matrix certificate: unexpected axiom {ax}"
  Lean.logInfo m!"{decl} depends on axioms: {axioms}"
