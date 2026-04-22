import Omega.SyncKernelWeighted.CarryFreeLeakage

namespace Omega.SyncKernelWeighted

/-- Three-coordinate resource profile: state count, internal zero-carry throughput, and leakage. -/
abbrev parallel_addition_zero_temp_pareto_frontier_resources := ℕ × ℕ × ℕ

/-- Mixed Pareto dominance: fewer states, greater internal throughput, and no more leakage. -/
def parallel_addition_zero_temp_pareto_frontier_dominates
    (A B : parallel_addition_zero_temp_pareto_frontier_resources) : Prop :=
  A.1 ≤ B.1 ∧ A.2.1 ≥ B.2.1 ∧ A.2.2 ≤ B.2.2

/-- `K9` resource triple from the audited zero-temperature carry-free data. -/
def parallel_addition_zero_temp_pareto_frontier_k9 :
    parallel_addition_zero_temp_pareto_frontier_resources :=
  (carryFreeCoreSize auditedKernelK9Core, zeroCarryOutdegree auditedKernelK9Core, k9ZeroCarryLeakage)

/-- `K13` resource triple from the audited zero-temperature carry-free data. -/
def parallel_addition_zero_temp_pareto_frontier_k13 :
    parallel_addition_zero_temp_pareto_frontier_resources :=
  (carryFreeCoreSize auditedKernelK13Core, zeroCarryOutdegree auditedKernelK13Core, k13ZeroCarryLeakage)

/-- `K21` resource triple from the audited zero-temperature carry-free data. -/
def parallel_addition_zero_temp_pareto_frontier_k21 :
    parallel_addition_zero_temp_pareto_frontier_resources :=
  (carryFreeCoreSize auditedKernelK21Core, k21CoreZeroCarryEdges, k21LeakingZeroCarryEdges)

/-- Concrete Pareto-frontier certificate for the three audited zero-temperature kernels. -/
def ParallelAdditionZeroTempParetoFrontierStatement : Prop :=
  parallel_addition_zero_temp_pareto_frontier_k9 = (7, 7, 0) ∧
    parallel_addition_zero_temp_pareto_frontier_k13 = (27, 27, 0) ∧
    parallel_addition_zero_temp_pareto_frontier_k21 = (21, 34, 71) ∧
    ¬ parallel_addition_zero_temp_pareto_frontier_dominates
        parallel_addition_zero_temp_pareto_frontier_k9
        parallel_addition_zero_temp_pareto_frontier_k13 ∧
    ¬ parallel_addition_zero_temp_pareto_frontier_dominates
        parallel_addition_zero_temp_pareto_frontier_k13
        parallel_addition_zero_temp_pareto_frontier_k9 ∧
    ¬ parallel_addition_zero_temp_pareto_frontier_dominates
        parallel_addition_zero_temp_pareto_frontier_k9
        parallel_addition_zero_temp_pareto_frontier_k21 ∧
    ¬ parallel_addition_zero_temp_pareto_frontier_dominates
        parallel_addition_zero_temp_pareto_frontier_k21
        parallel_addition_zero_temp_pareto_frontier_k9 ∧
    ¬ parallel_addition_zero_temp_pareto_frontier_dominates
        parallel_addition_zero_temp_pareto_frontier_k13
        parallel_addition_zero_temp_pareto_frontier_k21 ∧
    ¬ parallel_addition_zero_temp_pareto_frontier_dominates
        parallel_addition_zero_temp_pareto_frontier_k21
        parallel_addition_zero_temp_pareto_frontier_k13

/-- Paper label: `cor:parallel-addition-zero-temp-pareto-frontier`. -/
theorem paper_parallel_addition_zero_temp_pareto_frontier :
    ParallelAdditionZeroTempParetoFrontierStatement := by
  rcases paper_carry_free_core_block with ⟨hk9, hk13, hk21⟩
  rcases paper_carry_free_leakage with ⟨hk9leak, hk13leak, hk21core, hk21leak, _, _⟩
  have hk9_eq : parallel_addition_zero_temp_pareto_frontier_k9 = (7, 7, 0) := by
    rcases hk9 with ⟨hk9size, hk9out⟩
    simp [parallel_addition_zero_temp_pareto_frontier_k9, hk9size, hk9out, hk9leak]
  have hk13_eq : parallel_addition_zero_temp_pareto_frontier_k13 = (27, 27, 0) := by
    rcases hk13 with ⟨hk13size, hk13out⟩
    simp [parallel_addition_zero_temp_pareto_frontier_k13, hk13size, hk13out, hk13leak]
  have hk21_eq : parallel_addition_zero_temp_pareto_frontier_k21 = (21, 34, 71) := by
    rcases hk21 with ⟨hk21size, _, _⟩
    have hk21size' : carryFreeCoreSize auditedKernelK21Core = 21 := by
      rw [hk21size]
      norm_num
    simp [parallel_addition_zero_temp_pareto_frontier_k21, hk21size', hk21core, hk21leak]
  refine ⟨hk9_eq, hk13_eq, hk21_eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk9_eq, hk13_eq]
    norm_num [parallel_addition_zero_temp_pareto_frontier_dominates]
  · rw [hk9_eq, hk13_eq]
    norm_num [parallel_addition_zero_temp_pareto_frontier_dominates]
  · rw [hk9_eq, hk21_eq]
    norm_num [parallel_addition_zero_temp_pareto_frontier_dominates]
  · rw [hk9_eq, hk21_eq]
    norm_num [parallel_addition_zero_temp_pareto_frontier_dominates]
  · rw [hk13_eq, hk21_eq]
    norm_num [parallel_addition_zero_temp_pareto_frontier_dominates]
  · rw [hk13_eq, hk21_eq]
    norm_num [parallel_addition_zero_temp_pareto_frontier_dominates]

end Omega.SyncKernelWeighted
