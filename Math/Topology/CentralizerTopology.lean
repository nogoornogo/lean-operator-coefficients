import Mathlib.Topology.Algebra.Group.Basic
import Lean.Util.CollectAxioms

/-!
# Closed-graph property of centralizers

Only the checked sequential lemma from the local-prover draft is retained.
It does not assert that nearby centralizers are contained in a fixed subgroup.
The rejected neighborhood statement is preserved in `docs/history/e6-leanstral`.
-/

set_option autoImplicit false

open Filter Topology

namespace Math.CentralizerTopology

/-- A convergent sequence of commuting pairs has commuting limits.
The historical name denotes this sequential closed-graph statement only. -/
theorem centralizer_upperSemicontinuous {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [T2Space G] {g : G} {g_n : ℕ → G} {x : G} {x_n : ℕ → G}
    (hg : Tendsto g_n atTop (𝓝 g)) (hx : Tendsto x_n atTop (𝓝 x))
    (h_centralizer : ∀ n, x_n n ∈ Subgroup.centralizer ({g_n n} : Set G)) :
    x ∈ Subgroup.centralizer ({g} : Set G) := by
  have h_comm : ∀ n, x_n n * g_n n = g_n n * x_n n := by
    intro n
    simpa [Subgroup.mem_centralizer_singleton_iff] using h_centralizer n
  have h_mul_cont : Continuous (fun (p : G × G) => p.1 * p.2) := by fun_prop
  have h_mul_comm_cont : Continuous (fun (p : G × G) => p.2 * p.1) := by fun_prop
  have h_prod_tendsto : Tendsto (fun n => (x_n n, g_n n)) atTop (𝓝 (x, g)) :=
    Tendsto.prodMk_nhds hx hg
  have h_prod_mul : Tendsto (fun n => x_n n * g_n n) atTop (𝓝 (x * g)) :=
    (Continuous.tendsto h_mul_cont (x, g)).comp h_prod_tendsto
  have h_prod_mul_comm : Tendsto (fun n => g_n n * x_n n) atTop (𝓝 (g * x)) :=
    (Continuous.tendsto h_mul_comm_cont (x, g)).comp h_prod_tendsto
  have h_limits_eq : x * g = g * x := by
    have h_eq_seq : (fun n => x_n n * g_n n) = (fun n => g_n n * x_n n) := by
      ext n; exact h_comm n
    rw [h_eq_seq] at h_prod_mul
    exact tendsto_nhds_unique h_prod_mul h_prod_mul_comm
  simpa [Subgroup.mem_centralizer_singleton_iff] using h_limits_eq

end Math.CentralizerTopology

run_cmd do
  let decl := ``Math.CentralizerTopology.centralizer_upperSemicontinuous
  let axioms ← Lean.collectAxioms decl
  for ax in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "CentralizerTopology: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"CentralizerTopology: {decl} depends on axioms: {axioms}"
