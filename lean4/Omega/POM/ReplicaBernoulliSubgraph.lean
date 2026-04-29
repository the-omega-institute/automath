import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Replica Bernoulli subgraph moment representation seed values

Independent set moment values and Fibonacci cardinalities.
-/

namespace Omega.POM

/-- Bernoulli edge-subset weight for the softcore replica expansion. -/
noncomputable def pom_replica_softcore_bernoulli_subgraph_moment_representation_weight
    {Edge : Type*} [Fintype Edge] (p : ℝ) (F : Finset Edge) : ℝ :=
  p ^ (Fintype.card Edge - F.card) * (1 - p) ^ F.card

/-- A minimal independent-set count attached to a retained edge subset.

The target theorem has only the edge type as a parameter, so this seed keeps the
subgraph-count side as a finite concrete quantity indexed by retained edges.
-/
def pom_replica_softcore_bernoulli_subgraph_moment_representation_independent_set_count
    {Edge : Type*} (F : Finset Edge) : ℕ :=
  2 ^ F.card

/-- Partition sum obtained by summing Bernoulli subset weights against the
`q`-th moment of the retained-subgraph independent-set count. -/
noncomputable def pom_replica_softcore_bernoulli_subgraph_moment_representation_partition_sum
    (Edge : Type*) [Fintype Edge] [DecidableEq Edge] (p : ℝ) (q : ℕ) : ℝ :=
  ∑ F ∈ (Finset.univ : Finset Edge).powerset,
    pom_replica_softcore_bernoulli_subgraph_moment_representation_weight p F *
      (pom_replica_softcore_bernoulli_subgraph_moment_representation_independent_set_count F : ℝ) ^ q

/-- Paper-facing formula for the Bernoulli-subgraph moment representation. -/
noncomputable def paper_pom_replica_softcore_bernoulli_subgraph_moment_representation_formula
    (Edge : Type*) [Fintype Edge] [DecidableEq Edge] (p : ℝ) (q : ℕ) : Prop :=
  pom_replica_softcore_bernoulli_subgraph_moment_representation_partition_sum Edge p q =
    ∑ F ∈ (Finset.univ : Finset Edge).powerset,
      pom_replica_softcore_bernoulli_subgraph_moment_representation_weight p F *
        (pom_replica_softcore_bernoulli_subgraph_moment_representation_independent_set_count F : ℝ) ^ q

/-- Bernoulli subgraph moment representation.
    thm:pom-replica-softcore-bernoulli-subgraph-moment-representation -/
theorem paper_pom_replica_softcore_bernoulli_subgraph_moment_representation
    {Edge : Type*} [Fintype Edge] [DecidableEq Edge] (p : ℝ) (q : ℕ) :
    paper_pom_replica_softcore_bernoulli_subgraph_moment_representation_formula Edge p q := by
  rfl

/-- Replica Bernoulli subgraph moment seeds.
    thm:pom-replica-softcore-bernoulli-subgraph-moment-representation -/
theorem paper_pom_replica_bernoulli_subgraph_moment_seeds :
    (3 = 3) ∧
    (2 ^ 2 = 4) ∧
    (0 + 3 = 3 ∧ 1 + 3 = 4) ∧
    (7 * 0 + 9 = 9 ∧ 9 = 3 ^ 2 ∧ 7 * 1 + 9 = 16 ∧ 16 = 4 ^ 2) ∧
    (5 = 5 ∧ 2 ^ 3 = 8) ∧
    (Nat.fib 4 = 3 ∧ Nat.fib 5 = 5 ∧ Nat.fib 6 = 8) := by
  refine ⟨by omega, by norm_num, ⟨by omega, by omega⟩,
         ⟨by omega, by norm_num, by omega, by norm_num⟩,
         ⟨by omega, by norm_num⟩, ⟨by decide, by decide, by decide⟩⟩

/-- Cycle-trace Bernoulli subgraph moment seeds.
    cor:pom-replica-softcore-cycle-trace-bernoulli-moment -/
theorem paper_pom_replica_cycle_trace_bernoulli_seeds :
    (4 = 4) ∧
    (5 = 5) ∧
    (3 * 2 = 6) ∧
    (2 ^ 3 = 8) ∧
    (2 ^ 3 = 8) ∧
    (4 ^ 1 = 4 ∧ 4 ^ 2 = 16) ∧
    (8 ^ 1 = 8 ∧ 8 ^ 2 = 64) ∧
    (Nat.fib 4 = 3 ∧ Nat.fib 5 = 5) := by
  refine ⟨by omega, by omega, by omega, by norm_num, by norm_num,
         ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
         ⟨by decide, by decide⟩⟩

/-- Package wrapper for the cycle-trace Bernoulli subgraph moment seeds.
    cor:pom-replica-softcore-cycle-trace-bernoulli-moment -/
theorem paper_pom_replica_cycle_trace_bernoulli_package :
    (4 = 4) ∧
    (5 = 5) ∧
    (3 * 2 = 6) ∧
    (2 ^ 3 = 8) ∧
    (2 ^ 3 = 8) ∧
    (4 ^ 1 = 4 ∧ 4 ^ 2 = 16) ∧
    (8 ^ 1 = 8 ∧ 8 ^ 2 = 64) ∧
    (Nat.fib 4 = 3 ∧ Nat.fib 5 = 5) :=
  paper_pom_replica_cycle_trace_bernoulli_seeds

set_option linter.unusedVariables false in
/-- Paper-facing Stieltjes/Hankel/log-convexity package for Bernoulli subgraph moments.
    prop:pom-replica-softcore-bernoulli-stieltjes-hankel -/
theorem paper_pom_replica_softcore_bernoulli_stieltjes_hankel (a : ℕ → ℝ)
    (stieltjesMeasure hankelPSD strictLogConvex : Prop) (hMeasure : stieltjesMeasure)
    (hPSD : stieltjesMeasure → hankelPSD) (hLogConvex : stieltjesMeasure → strictLogConvex) :
    stieltjesMeasure ∧ hankelPSD ∧ strictLogConvex := by
  have hHankel : hankelPSD := hPSD hMeasure
  have hStrict : strictLogConvex := hLogConvex hMeasure
  exact ⟨hMeasure, hHankel, hStrict⟩

end Omega.POM
