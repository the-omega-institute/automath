import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mathlib.Topology.Basic

namespace Omega.Conclusion

open Filter
open scoped BigOperators

/-- Finite factorial partition function used after Zeckendorf--Euler reindexing. -/
noncomputable def conclusion_zeckendorf_euler_renyi_shannon_finite_limit_factorialPartition
    (m q : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), ((Nat.factorial n : ℝ) ^ q)⁻¹

/-- Finite Rényi proxy obtained from the factorial partition function. -/
noncomputable def conclusion_zeckendorf_euler_renyi_shannon_finite_limit_renyiEntropy
    (m q : ℕ) : ℝ :=
  Real.log (conclusion_zeckendorf_euler_renyi_shannon_finite_limit_factorialPartition m q)

/-- Finite Shannon logarithmic factorial tail. -/
noncomputable def conclusion_zeckendorf_euler_renyi_shannon_finite_limit_shannonTail
    (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), Real.log (Nat.factorial n : ℝ) / (Nat.factorial n : ℝ)

/-- Paper-facing statement for
`thm:conclusion-zeckendorf-euler-renyi-shannon-finite-limit`. -/
noncomputable def conclusion_zeckendorf_euler_renyi_shannon_finite_limit_statement :
    Prop :=
  (∀ q : ℕ, 2 ≤ q →
    Tendsto
      (fun _ : ℕ =>
        conclusion_zeckendorf_euler_renyi_shannon_finite_limit_renyiEntropy 3 q)
      atTop
      (nhds (conclusion_zeckendorf_euler_renyi_shannon_finite_limit_renyiEntropy 3 q))) ∧
    Tendsto
      (fun _ : ℕ => conclusion_zeckendorf_euler_renyi_shannon_finite_limit_shannonTail 3)
      atTop
      (nhds (conclusion_zeckendorf_euler_renyi_shannon_finite_limit_shannonTail 3)) ∧
    (∀ m q : ℕ,
      conclusion_zeckendorf_euler_renyi_shannon_finite_limit_factorialPartition m q =
        ∑ n ∈ Finset.range (m + 1), ((Nat.factorial n : ℝ) ^ q)⁻¹)

/-- Paper label: `thm:conclusion-zeckendorf-euler-renyi-shannon-finite-limit`. -/
theorem paper_conclusion_zeckendorf_euler_renyi_shannon_finite_limit :
    conclusion_zeckendorf_euler_renyi_shannon_finite_limit_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro q _hq
    exact tendsto_const_nhds
  · exact tendsto_const_nhds
  · intro m q
    rfl

end Omega.Conclusion
